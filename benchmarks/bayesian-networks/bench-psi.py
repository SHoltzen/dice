import os
import subprocess

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
            output = subprocess.run('timeout 180m (time (psi %s))' % (f), shell=True, stderr=subprocess.STDOUT)
            output = subprocess.run('time 180m ((psi --dp %s))' % (f), shell=True, stderr=subprocess.STDOUT)
