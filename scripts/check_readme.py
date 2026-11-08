#!/usr/bin/env python3
"""Compile the README's Lean statements against the public library."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PRELUDE = """import GaussianTesting
open GaussianTesting
open scoped InnerProductSpace
namespace ReadmeExamples
"""


def lean_examples(markdown):
    """Keep the displayed statements, isolating their names from the library."""
    blocks = list(re.finditer(r'^```lean[ \t]*\n(.*?)^```[ \t]*$', markdown, re.M | re.S))
    if not blocks:
        raise ValueError('README contains no Lean examples to check.')
    examples = [PRELUDE]
    for match in blocks:
        line = markdown.count('\n', 0, match.start()) + 2
        examples.append(f'\n-- README example starting at line {line}.\n{match[1]}')
    examples.append('\nend ReadmeExamples\n')
    return ''.join(examples), len(blocks)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('readme', nargs='?', type=Path, default=ROOT / 'README.md')
    args = parser.parse_args()
    source, count = lean_examples(args.readme.read_text(encoding='utf-8'))
    with tempfile.TemporaryDirectory(prefix='gaussian-readme-') as directory:
        path = Path(directory) / 'ReadmeExamples.lean'
        path.write_text(source, encoding='utf-8')
        result = subprocess.run(
            ['lake', 'env', 'lean', '-DwarningAsError=true', str(path)], cwd=ROOT)
        if result.returncode:
            raise SystemExit(result.returncode)
    print(f'Lean checked all {count} README examples.')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError) as error:
        raise SystemExit(str(error)) from error
