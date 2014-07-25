#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SELF="$(readlink -f "${BASH_SOURCE[0]}")"

cd "$DIR/../src"

# update makefile if we're newer
if [ "$SELF" -nt "$DIR/../src/Makefile.librarydepgraphs" ] || [ "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh -nt "$DIR/../src/Makefile.librarydepgraphs" ]
then
    echo "Making makefile"
    bash "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh ../src/Makefile.librarydepgraphs -t x86proved -c x86/=Magenta -c charge/=BlueViolet -c examples/=Orange -c tools/=Cyan4 -R x86proved=.
    rm -f "$DIR/../src/library.svg" "$DIR/../src/library.dot"
fi

cd "$DIR/../src"
make -f Makefile.librarydepgraphs library.deps library.dot library.svg
