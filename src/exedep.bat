@echo off
@for %%X in (%*) do (@echo %%X: %%~pX%%~nX.hex 
@echo %%~pX%%~nX.hex: %%~pX%%~nX.vo)