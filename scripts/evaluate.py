#!/usr/bin/env python3
"""Evaluate translation or solver performance on the benchmark corpora."""

import argparse
import importlib
import sys


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    commands = {
        "translate": ("translation", "Translate and typecheck one archive"),
        "solvers": ("solvers", "Run SMT/CHC solvers on the paper or Flex corpus"),
        "campaign": ("campaign", "Run or resume the audited translation campaign"),
    }
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=commands,
                        help="; ".join(f"{name}: {help}" for name, (_, help) in commands.items()))
    if not argv or argv[0] in ("-h", "--help"):
        parser.print_help()
        return 0
    options = parser.parse_args(argv[:1])
    module = importlib.import_module("evaluation." + commands[options.command][0])
    return module.main(argv[1:])


if __name__ == "__main__":
    sys.exit(main())
