import os
import subprocess
from multiprocessing import Pool


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
            output = subprocess.run('time psi %s; echo %s' % (f, f), shell=True, stderr=subprocess.STDOUT)
            output = subprocess.run('time psi --dp %s' % (f), shell=True, stderr=subprocess.STDOUT)

time.sleep(10800)
os.sys('pkill psi')
