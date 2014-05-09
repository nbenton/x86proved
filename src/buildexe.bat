@echo off
rem Build example EXE image

coqc -dont-load-proofs -I x86 -I charge x86\%1.v >%1.hex
x86\bin\hexbin %1.hex %1.exe


