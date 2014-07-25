#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

cd "$DIR/../src"

# update makefile if we're newer
# FIXME: this test doesn't work super-well
if [ "${BASH_SOURCE[0]}" -nt "$DIR/../src/Makefile.librarydepgraphs" ] || [ "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh -nt "$DIR/../src/Makefile.librarydepgraphs" ]
then
    echo "Making makefile"
    . "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh ../src/Makefile.librarydepgraphs -t x86proved -c src/x86/=Magenta -c src/charge/=BlueViolet -c src/examples/=Orange -c src/tools/=Cyan4 -R x86proved=src/
    rm -f "$DIR/../src/library.svg" "$DIR/../src/library.dot"
fi

cd "$DIR/../src"
make -f Makefile.librarydepgraphs library.deps library.dot library.svg
