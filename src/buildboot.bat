rem Build boot loader

set TOOLSDIR=build
set PATH=%TOOLSDIR%;%PATH%

cd boot\SingLdrPc
call build
cd ..\..
cd boot\BootSectors
call build
cd ..\..
rem copy boot\obj\loader x86\bin\iso_dir

