@echo off
rem Build ISO image, assuming boot loader and all coq has been built

tools\hexbin x86\lifemain.hex ..\bin\iso_dir\iso.bin
copy boot\obj\loader ..\bin\iso_dir
..\build\cdimage -j1 -liSO -bboot\obj\etfs.bin ..\bin\iso_dir ..\bin\iso.iso
