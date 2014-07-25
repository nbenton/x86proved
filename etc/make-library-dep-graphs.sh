#!/usr/bin/env bash
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
SELF="$(readlink -f "${BASH_SOURCE[0]}")"

cd "$DIR/../src"

# update makefile if we're newer
if [ "$SELF" -nt "$DIR/../src/Makefile.librarydepgraphs" ] || [ "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh -nt "$DIR/../src/Makefile.librarydepgraphs" ]
then
    echo "Making makefile"
    # colors for directories come from the list at http://hackage.haskell.org/package/graphviz-2999.13.0.3/docs/Data-GraphViz-Attributes-Colors-X11.html#t:X11Color
    bash "$DIR"/coq-scripts/depgraphs/library/make-makefile.sh ../src/Makefile.librarydepgraphs -t x86proved -R x86proved=. \
	-c x86/=Magenta \
	-c charge/=BlueViolet \
	-c examples/=Orange \
	-c tools/=Cyan4

    rm -f "$DIR/../src/library.svg" "$DIR/../src/library.dot"
fi

cd "$DIR/../src"
make -f Makefile.librarydepgraphs library.deps library.dot library.svg
