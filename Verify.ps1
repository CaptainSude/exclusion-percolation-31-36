param(
    [string]$LakePath = 'lake'
)

$ErrorActionPreference = 'Stop'
$taskOldLocation = Get-Location
$taskOldLeanThreads = $env:LEAN_NUM_THREADS
$taskOutputDirectory = Join-Path $PSScriptRoot 'verification/local'
$taskReportPath = Join-Path $taskOutputDirectory 'status.json'
$taskLogPath = Join-Path $taskOutputDirectory 'full-build.log'
$taskReportStarted = $false
try {
    Set-Location -LiteralPath $PSScriptRoot
    if (-not $env:LEAN_NUM_THREADS) { $env:LEAN_NUM_THREADS = '1' }
    New-Item -ItemType Directory -Path $taskOutputDirectory -Force | Out-Null
    [ordered]@{
        startedAtUtc = (Get-Date).ToUniversalTime().ToString('o')
        result = 'running'
    } | ConvertTo-Json | Set-Content -LiteralPath $taskReportPath -Encoding UTF8
    $taskReportStarted = $true
    Set-Content -LiteralPath $taskLogPath -Value '' -Encoding UTF8

    $taskVersion = & $LakePath env lean --version 2>&1
    if ($LASTEXITCODE -ne 0) { throw 'Cannot run the pinned Lean toolchain.' }
    if (($taskVersion -join "`n") -notmatch 'Lean \(version 4\.34\.1[,\)]') {
        throw "Expected Lean 4.34.1. Found: $taskVersion"
    }

    function Get-TaskSourceHashes {
        $taskSources = @(
            Get-ChildItem -LiteralPath $PSScriptRoot -Filter '*.lean' -File
            Get-ChildItem -LiteralPath (Join-Path $PSScriptRoot 'ExceptionalTimes') -Filter '*.lean' -File -Recurse
        ) | Sort-Object FullName
        foreach ($taskSource in $taskSources) {
            [ordered]@{
                path = $taskSource.FullName.Substring($PSScriptRoot.Length + 1).Replace('\', '/')
                sha256 = (Get-FileHash -LiteralPath $taskSource.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
            }
        }
    }

    $taskBeforeHashes = @(Get-TaskSourceHashes)
    $taskAuditText = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'ExceptionalTimes/AxiomAudit.lean') -Raw
    foreach ($taskSource in $taskBeforeHashes) {
        if ($taskSource.path -eq 'lakefile.lean' -or $taskSource.path -eq 'ExceptionalTimes/AxiomAudit.lean') { continue }
        $taskModule = $taskSource.path.Replace('/', '.').Replace('.lean', '')
        if ($taskAuditText -notmatch ('(?m)^import ' + [regex]::Escape($taskModule) + '\s*$')) {
            throw "AxiomAudit does not import project module $taskModule."
        }
    }

    & $LakePath --wfail build 2>&1 |
        Tee-Object -FilePath $taskLogPath
    $taskBuildExit = $LASTEXITCODE
    if ($taskBuildExit -ne 0) { throw "Lean build failed: exit $taskBuildExit." }

    $taskLog = Get-Content -LiteralPath $taskLogPath -Raw
    if ($taskLog -match '\bsorryAx\b') { throw 'An audited declaration uses sorryAx.' }
    $taskHashes = @(Get-TaskSourceHashes)
    if (($taskBeforeHashes | ConvertTo-Json -Compress) -ne ($taskHashes | ConvertTo-Json -Compress)) {
        throw 'Project sources changed during verification. Run again after all source edits finish.'
    }

    $taskManifest = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lake-manifest.json') -Raw | ConvertFrom-Json
    $taskMathlib = @($taskManifest.packages | Where-Object { $_.name -eq 'mathlib' })
    if ($taskMathlib.Count -ne 1) { throw 'Expected one mathlib revision in lake-manifest.json.' }
    [ordered]@{
        checkedAtUtc = (Get-Date).ToUniversalTime().ToString('o')
        result = 'passed'
        leanVersion = ($taskVersion -join "`n")
        mathlibCommit = $taskMathlib[0].rev
        buildExitCode = $taskBuildExit
        warningsAreErrors = $true
        mainTheorem = 'ExceptionalTimes.PublishedNearestNeighborDimension.exists_realization_dimension'
        literatureInputs = 'Explicit theorem hypotheses; see docs/literature.md.'
        sources = @($taskHashes)
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath $taskReportPath -Encoding UTF8
    Write-Output 'All project modules and the main theorem checked. Record saved in verification/local/.'
}
catch {
    if ($taskReportStarted) {
        [ordered]@{
            checkedAtUtc = (Get-Date).ToUniversalTime().ToString('o')
            result = 'failed'
            error = $_.Exception.Message
        } | ConvertTo-Json | Set-Content -LiteralPath $taskReportPath -Encoding UTF8
    }
    throw
}
finally {
    Set-Location -LiteralPath $taskOldLocation.Path
    $env:LEAN_NUM_THREADS = $taskOldLeanThreads
}
