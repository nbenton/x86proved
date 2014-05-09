@echo off
rem Build ISO image, assuming boot loader and all coq has been built

coqc -dont-load-proofs -I . -I x86 -I charge x86\main.v >iso.hex
tools\hexbin iso.hex x86\bin\iso_dir\iso.bin

tools\cdimage -j1 -liSO -bx86\bin\etfs.bin x86\bin\iso_dir x86\bin\iso.iso

