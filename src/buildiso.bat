@echo off
rem Build ISO image, assuming boot loader and all coq has been built
rem IMPORTANT PROBLEM: 
rem There is a problem with hyperv, if you write to the ISO file registered
rem and already booted at least once as a DVD with a virtual machine, then on restarting that machine 
rem it will fail to boot with a message "Boot failure. Reboot and Select proper Boot device..."
rem SOLUTION: Virutal-Eject the DVD and reload it.
rem
tools\hexbin x86\lifemain.hex ..\bin\iso_dir\iso.bin
rem This one is buggy
copy boot\obj\loader ..\bin\iso_dir
..\build\cdimage -j1 -liSO -bboot\obj\etfs.bin ..\bin\iso_dir ..\bin\iso.iso
