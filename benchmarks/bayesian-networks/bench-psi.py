import os
import subprocess
from multiprocessing import Pool

import asyncio

async def run(cmd):
    proc = await asyncio.create_subprocess_shell(
        cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE)

    stdout, stderr = await proc.communicate()

    print(f'[{cmd!r} exited with {proc.returncode}]')
    if stdout:
        print(f'[stdout]\n{stdout.decode()}')
    if stderr:
        print(f'[stderr]\n{stderr.decode()}')



rootdir = '.'
extensions = ('.psi')


processes = []
# for file in files_output:
#     f = os.tmpfile()
#     p = subprocess.Popen(['md5sum',file],stdout=f)
#     processes.append((p, f))

for subdir, dirs, files in os.walk(rootdir):
    for f in files:
        ext = os.path.splitext(f)[-1].lower()
        if ext in extensions:
            asyncio.run(run('time psi %s' % f))
            asyncio.run(run('time psi --dp %s' % f))

time.sleep(10800)
os.sys('pkill psi')
