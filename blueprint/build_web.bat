@echo off
REM Build leanblueprint web with UTF-8 encoding support for Windows
REM This fixes UnicodeEncodeError with Greek letters like π in \lean{} commands

REM Force Python to use UTF-8
set PYTHONIOENCODING=utf-8
set PYTHONUTF8=1

REM Set console to UTF-8
chcp 65001 >nul 2>&1

REM Change to blueprint directory
cd /d "%~dp0"

REM Add current directory to PYTHONPATH for sitecustomize.py
set PYTHONPATH=%~dp0;%PYTHONPATH%

echo Building leanblueprint web with UTF-8 encoding...
leanblueprint web

if %ERRORLEVEL% NEQ 0 (
    echo.
    echo Build failed. If you see encoding errors, try running:
    echo   set PYTHONUTF8=1
    echo   leanblueprint web
    pause
)
