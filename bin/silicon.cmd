@echo off
setlocal

set BIN=%~dp0
set ROOT=%BIN%..

pushd %ROOT%
call mill vercors.main.runScript
popd

set Z3="%ROOT%\res\universal\deps\win\z3\bin\z3.exe"

call "%ROOT%\out\vercors\main\runScript.dest\silicon" --z3Exe %Z3% %*