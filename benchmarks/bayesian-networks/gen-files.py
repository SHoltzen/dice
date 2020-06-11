import os
rootdir = '.'
extensions = ('.bif')

for subdir, dirs, files in os.walk(rootdir):
    for f in files:
        ext = os.path.splitext(f)[-1].lower()
        if ext in extensions:
            os.system('~/Documents/Programming/bngen/Main.native sym %s > %s.dice' % (f, f))
            os.system('~/Documents/Programming/bngen/Main.native psi %s > %s.psi' % (f, f))
