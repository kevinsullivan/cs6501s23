# Notes

Update mkall.sh when the set of source files changes. When that happens, regenerate the corresponding .inc files under projectdir/source/<dirs> by running ./mkall.sh from the parent of this directory. It in turn will run ./mkdoc.py on each file named in mkall.sh. Finish html or latex generation using make html or make latex.