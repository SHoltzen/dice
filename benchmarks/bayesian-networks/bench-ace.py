import os
import subprocess
from multiprocessing import Pool



import asyncio


from multiprocessing import Pool

def bench(x):
    os.system('time %s' % x)
    print("result for %s" % x)
    # l.append(run('time psi --dp %s' % f))


rootdir = '.'
extensions = ('.net')


processes = []
# for file in files_output:
#     f = os.tmpfile()
#     p = subprocess.Popen(['md5sum',file],stdout=f)
#     processes.append((p, f))

l = []
for subdir, dirs, files in os.walk(rootdir):
    for f in files:
        ext = os.path.splitext(f)[-1].lower()
        if ext in extensions:
            l.append('~/Downloads/ace_v3.0_osx/compile %s' % f)


if __name__ == '__main__':
    with Pool(10) as p:
        print(p.map(bench, l))

