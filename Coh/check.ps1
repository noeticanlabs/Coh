Write-Host "--- Starting Local CI Simulation ---" -ForegroundColor Cyan

# Ensure we are in the right directory
if (!(Test-Path lakefile.lean)) {
    Write-Error "Error: lakefile.lean not found. Please run this script from the package directory (Coh/)."
    exit 1
}

$lake = "C:\Users\truea\.elan\bin\lake.exe"

# 1. Build Core
Write-Host "Building core modules..." -ForegroundColor Yellow
& $lake build
if ($LASTEXITCODE -ne 0) { 
    Write-Host "Error: Core build failed!" -ForegroundColor Red
    exit 1 
}

# 2. Run Tests
Write-Host "Building and running regression tests..." -ForegroundColor Yellow
& $lake build FiniteWordTests
if ($LASTEXITCODE -ne 0) { 
    Write-Host "Error: Test build failed!" -ForegroundColor Red
    exit 1 
}
Write-Host "Executing FiniteWordTests..." -ForegroundColor Gray
& ./.lake/build/bin/FiniteWordTests.exe

# 3. Sorry Check
Write-Host "Scanning for 'sorry' markers in Coh/..." -ForegroundColor Yellow
$sorries = Get-ChildItem -Path ./Coh -Recurse -Filter *.lean | Select-String "sorry"
if ($sorries) {
    Write-Host "Error: Found 'sorry' markers in core library:" -ForegroundColor Red
    $sorries | ForEach-Object { Write-Host "  $($_.Path):$($_.LineNumber)" -ForegroundColor Red }
    exit 1
}

Write-Host "--- Local CI Simulation Passed ---" -ForegroundColor Green
