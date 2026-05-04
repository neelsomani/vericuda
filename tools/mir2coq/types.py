"""Type classification for MIR variable declarations."""

from __future__ import annotations

import dataclasses
from typing import Dict, Optional, Set


@dataclasses.dataclass
class TypeInfo:
    kind: str  # "scalar", "ptr", "ref", "other"
    mir_ty: Optional[str]
    element: Optional[str] = None  # for pointers / refs


TYPE_ALIASES: Dict[str, str] = {
    "usize": "TyU64",
    "isize": "TyI32",
    "i32": "TyI32",
    "u32": "TyU32",
    "f32": "TyF32",
    "bool": "TyBool",
}

SYMBOLIC_CONSTS: Dict[str, str] = {
    "i128::MIN": "i128_MIN",
    "TILE_SIZE": "TILE_SIZE",
    "TILE_SIZE_2D": "TILE_SIZE_2D",
    "gemm::TILE_SIZE": "gemm_tiled_TILE_SIZE",
    "gemm::TILE_SIZE_2D": "gemm_tiled_TILE_SIZE_2D",
}

CUDA_INTRINSICS: Set[str] = {
    "block_dim_x", "block_dim_y", "block_dim_z",
    "block_idx_x", "block_idx_y", "block_idx_z",
    "thread_idx_x", "thread_idx_y", "thread_idx_z",
    "grid_dim_x", "grid_dim_y", "grid_dim_z",
    "index_1d",
    "sync_threads", "syncthreads",
}


def classify_type(raw: str) -> TypeInfo:
    raw = raw.strip()

    if raw.startswith("&"):
        elem = raw[1:].strip()
        elem_ty = pointee_type(elem)
        return TypeInfo(kind="ref", mir_ty="TyU64", element=elem_ty)

    if raw.startswith("*const") or raw.startswith("*mut"):
        elem = raw.split(None, 1)[1]
        elem_ty = pointee_type(elem)
        return TypeInfo(kind="ptr", mir_ty="TyU64", element=elem_ty)

    alias = TYPE_ALIASES.get(raw)
    if alias:
        return TypeInfo(kind="scalar", mir_ty=alias)

    if "AtomicU32" in raw:
        return TypeInfo(kind="other", mir_ty="TyU32")

    return TypeInfo(kind="other", mir_ty=None)


def pointee_type(raw: str) -> str:
    raw = raw.strip()
    if "AtomicU32" in raw:
        return "TyU32"
    alias = TYPE_ALIASES.get(raw)
    return alias or "TyU32"
