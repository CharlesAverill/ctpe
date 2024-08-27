python compile.py && sh convert.sh notest $1 && git add . && git commit -m "Update $(date +"%Y-%m-%d %H:%M:%S")" && git push
