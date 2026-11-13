"""Run the executable checks: every checks/haskell/Check*.hs, compiled with
`ghc -O1` and run.

Each program prints "ok <scope>: N checks" and exits non-zero on a failed
check. The shared modules of the directory (the languages, their semantics) are
found through `-i`. Nothing is installed: the programs use base only. The
objects go to `$BUILD_CACHE/haskell` when BUILD_CACHE is set (so unchanged
modules are not compiled again), otherwise to a temporary directory.
"""
from pathlib import Path
import os
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
HASKELL = ROOT / 'checks' / 'haskell'


def run(program, objects):
    out = objects / program.stem
    out.mkdir(parents=True, exist_ok=True)
    binary = out / program.stem
    compiled = subprocess.run(
        ['ghc', '-O1', '-v0', f'-i{HASKELL}', f'-outputdir={out}',
         '-o', str(binary), str(program)],
        cwd=ROOT, capture_output=True, text=True)
    if compiled.returncode != 0:
        return compiled
    return subprocess.run([str(binary)], cwd=ROOT, capture_output=True,
                          text=True)


def main():
    programs = sorted(HASKELL.glob('Check*.hs'))
    if not programs:
        sys.exit('no checks/haskell/Check*.hs')
    cache = os.environ.get('BUILD_CACHE')
    with tempfile.TemporaryDirectory() as temporary:
        objects = (Path(os.path.expanduser(cache)) / 'haskell' if cache
                   else Path(temporary))
        failed = []
        for program in programs:
            start = time.monotonic()
            result = run(program, objects)
            output = (result.stdout + result.stderr).strip()
            last = (output.splitlines()[-1] if output
                    else f'{program.name}: no output')
            print(f'{last} ({time.monotonic() - start:.0f} s)')
            if result.returncode != 0 \
                    or not result.stdout.strip().startswith('ok '):
                failed.append(program.name)
                print(output, file=sys.stderr)
    if failed:
        sys.exit('failed: ' + ', '.join(failed))


if __name__ == '__main__':
    main()
