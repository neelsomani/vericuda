#!/usr/bin/env python3
"""Entry-point wrapper for the mir2coq package.

The actual implementation lives in the mir2coq/ package directory alongside
this file.  Running this script directly (as the Makefile does) works because
Python adds the script's own directory (tools/) to sys.path, making the
mir2coq package importable.
"""

import sys
from mir2coq import main

if __name__ == "__main__":
    sys.exit(main())
