@ECHO OFF

REM ========== COPYRIGHT/COPYLEFT ==========

REM (C) 2016 Intel Deutschland GmbH
REM Author: Michael Soegtrop

REM Released to the public by Intel under the
REM GNU Lesser General Public License Version 2.1 or later
REM See https://www.gnu.org/licenses/old-licenses/lgpl-2.1.html

REM ========== BUILD COQ ==========

call MakeCoq_SetRootPath

call MakeCoq_MinGW.bat ^
  -arch=64 ^
  -mode=absolute ^
  -ocaml=Y ^
  -make=Y ^
  -coqver=git-v8.6 ^
  -destcyg="%ROOTPATH%\cygwin_coq64_86git_abs" ^
  -destcoq="%ROOTPATH%\coq64_86git_abs"

IF %ERRORLEVEL% NEQ 0 (
  ECHO MakeCoq_86git_abs_ocaml.bat failed with error code %ERRORLEVEL%
  EXIT /b %ERRORLEVEL%
)
