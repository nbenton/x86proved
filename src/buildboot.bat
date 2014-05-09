rem Build iSO boot loader, also hexbin tool

set TOOLSDIR=verve\base\build
set PATH=%TOOLSDIR%;%PATH%

cd x86\BootLoader\SingLdrPc
call build
cd ..\..\..
cd x86\BootLoader\BootSectors
call build
cd ..\..\..
copy x86\BootLoader\obj\loader x86\bin\iso_dir

cl hexbin.c /Fex86\bin\hexbin.exe


