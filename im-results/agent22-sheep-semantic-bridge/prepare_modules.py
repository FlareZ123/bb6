"""Expose verified standalone Lean modules for cross-project imported builds."""
from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

from filelock import FileLock


def prepare(path: Path) -> None:
    with FileLock(str(path) + '.lock'):
        source = path.read_text(encoding='utf-8')
        lines = source.splitlines(keepends=True)
        imports = []
        while lines and lines[0].startswith('import '):
            imports.append(lines.pop(0).replace('import ', 'public import ', 1))
        if not imports:
            raise ValueError(f'{path} does not start with Lean imports')
        transformed = 'module\n\n' + ''.join(imports) + '\n@[expose] public section\n\n' + ''.join(lines)
        with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, encoding='utf-8', delete=False) as tmp:
            name = Path(tmp.name)
            tmp.write(transformed)
            tmp.flush()
            os.fsync(tmp.fileno())
        try:
            os.replace(name, path)
        finally:
            name.unlink(missing_ok=True)


if __name__ == '__main__':
    for file in sys.argv[1:]:
        prepare(Path(file))
