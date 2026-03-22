use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let available = cuq_examples::TARGETS;
    if available.is_empty() {
        return Err("no tests were found under examples/test".into());
    }

    let selection = parse_target()?;
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

    match selection {
        TargetSelection::All => {
            for target in available {
                compile_target(&manifest_dir, target)?;
            }
        }
        TargetSelection::Single(target) => {
            if !available.contains(&target.as_str()) {
                return Err(format!(
                    "unknown target '{target}'. Available targets: {}",
                    available.join(", ")
                ));
            }
            compile_target(&manifest_dir, &target)?;
        }
    }

    Ok(())
}

fn compile_target(manifest_dir: &Path, target: &str) -> Result<(), String> {
    let mir_dir = manifest_dir.join("mir_dumps").join(target);
    if mir_dir.exists() {
        fs::remove_dir_all(&mir_dir)
            .map_err(|err| format!("failed to clear {:?}: {err}", mir_dir))?;
    }
    fs::create_dir_all(&mir_dir)
        .map_err(|err| format!("failed to create {:?}: {err}", mir_dir))?;

    println!("[cargo] dumping MIR for {target} -> {}", mir_dir.display());

    let mut rustflags = env::var("RUSTFLAGS").unwrap_or_default();
    if !rustflags.is_empty() {
        rustflags.push(' ');
    }
    rustflags.push_str("-Zunstable-options -Z dump-mir=PreCodegen -Z dump-mir-dir=");
    rustflags.push_str(
        mir_dir
            .to_str()
            .ok_or_else(|| format!("non-UTF8 path for {:?}", mir_dir))?,
    );

    let mut command = Command::new("cargo");
    command
        .arg("rustc")
        .arg("--manifest-path")
        .arg(manifest_dir.join("Cargo.toml"))
        .arg("--lib")
        .env("RUSTFLAGS", rustflags)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .arg("--")
        .arg("--crate-type=lib")
        .arg("--cfg")
        .arg(format!("target_name=\"{}\"", target));

    let status = command
        .status()
        .map_err(|err| format!("failed to spawn cargo rustc: {err}"))?;

    if !status.success() {
        return Err(format!("cargo rustc failed when building '{target}'"));
    }

    prune_mir_dir(&mir_dir, target)?;

    Ok(())
}

enum TargetSelection {
    All,
    Single(String),
}

fn parse_target() -> Result<TargetSelection, String> {
    let mut args = env::args().skip(1);
    let mut target: Option<String> = None;

    while let Some(arg) = args.next() {
        if arg == "--target" {
            let value = args
                .next()
                .ok_or_else(|| "--target requires a value".to_string())?;
            target = Some(value);
        } else if let Some(value) = arg.strip_prefix("--target=") {
            target = Some(value.to_string());
        } else {
            return Err(format!("unrecognized argument: {arg}"));
        }
    }

    Ok(match target {
        Some(value) => TargetSelection::Single(value),
        None => TargetSelection::All,
    })
}

fn prune_mir_dir(mir_dir: &Path, module: &str) -> Result<(), String> {
    let prefix = format!("cuq_examples.{module}-");
    let entries = fs::read_dir(mir_dir)
        .map_err(|err| format!("failed to read {:?}: {err}", mir_dir))?;

    for entry in entries {
        let entry = entry.map_err(|err| format!("failed to walk {:?}: {err}", mir_dir))?;
        let path = entry.path();
        let metadata = entry
            .metadata()
            .map_err(|err| format!("failed to stat {:?}: {err}", path))?;

        if metadata.is_dir() {
            fs::remove_dir_all(&path)
                .map_err(|err| format!("failed to remove {:?}: {err}", path))?;
            continue;
        }

        let keep = entry
            .file_name()
            .to_str()
            .map(|name| name.starts_with(&prefix))
            .unwrap_or(false);

        if !keep {
            fs::remove_file(&path)
                .map_err(|err| format!("failed to remove {:?}: {err}", path))?;
        }
    }

    Ok(())
}
