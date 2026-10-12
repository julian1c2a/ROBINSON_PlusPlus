# sondeos_todos.ps1 [PARALELO] [MINUTOS] — compila los sondeos de `sondeos/`, uno a uno (o N a la vez),
# cada uno con tiempo límite; escribe una tabla «fichero|exit|segundos|primer error» (c4 de ADR-117).
# Rescatado al árbol el 2026-10-12 (ADR-132, T00 de doc/AUDITORIA-SUELO-2026-10-12.md): es el que produjo las
# tablas de sondeos/pasadas/. Sólo cambian las rutas, ahora relativas al repo. ⚠️ Compila con `lake env lean`,
# que NO recibe los leanOptions del lakefile (autoImplicit): pasarlo a `lake lean` es T06, que lo medirá antes.
# Ejecutar desde PowerShell (lake no está en el PATH de Git Bash).
param([int]$Paralelo = 2, [int]$Minutos = 6)
$W = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$O = Join-Path $W "sondeos\pasadas\salida"   # fuera de git (.gitignore)
New-Item -ItemType Directory -Force $O | Out-Null
Set-Location $W
$ficheros = Get-ChildItem sondeos -Filter *.lean | Sort-Object Name
$cola = [System.Collections.Queue]::new(); $ficheros | ForEach-Object { $cola.Enqueue($_) }
$vivos = @{}
$tabla = [System.Collections.ArrayList]::new()
function Cierra($f, $p, $t0, $timeout) {
  $out = "$O\$($f.BaseName).out"; $err = "$O\$($f.BaseName).err"
  $secs = [Math]::Round(((Get-Date) - $t0).TotalSeconds)
  $txt = @(Get-Content $out, $err -ErrorAction SilentlyContinue)
  $e1 = ($txt | Where-Object { $_ -match 'error' } | Select-Object -First 1)
  if ($null -eq $e1) { $e1 = "" }
  $e1 = $e1 -replace '^.*?sondeos[\\/]', '' -replace '\|', '¦'
  if ($e1.Length -gt 200) { $e1 = $e1.Substring(0, 200) }
  $code = if ($timeout) { "TIMEOUT" } else { "$($p.ExitCode)" }
  [void]$tabla.Add("$($f.Name)|$code|$secs|$e1")
}
while ($cola.Count -gt 0 -or $vivos.Count -gt 0) {
  while ($cola.Count -gt 0 -and $vivos.Count -lt $Paralelo) {
    $f = $cola.Dequeue()
    $p = Start-Process lake -ArgumentList "env lean sondeos/$($f.Name)" -NoNewWindow -PassThru `
          -RedirectStandardOutput "$O\$($f.BaseName).out" -RedirectStandardError "$O\$($f.BaseName).err"
    $vivos[$f.Name] = @{ f = $f; p = $p; t0 = Get-Date }
  }
  Start-Sleep -Milliseconds 500
  foreach ($k in @($vivos.Keys)) {
    $v = $vivos[$k]
    if ($v.p.HasExited) { Cierra $v.f $v.p $v.t0 $false; $vivos.Remove($k) }
    elseif (((Get-Date) - $v.t0).TotalMinutes -gt $Minutos) {
      taskkill /PID $v.p.Id /T /F | Out-Null; Cierra $v.f $v.p $v.t0 $true; $vivos.Remove($k)
    }
  }
}
$tabla | Sort-Object | Set-Content -Encoding utf8 "$O\_tabla.txt"
$ok = @($tabla | Where-Object { ($_ -split '\|')[1] -eq '0' }).Count
$to = @($tabla | Where-Object { ($_ -split '\|')[1] -eq 'TIMEOUT' }).Count
"sondeos: $($tabla.Count) · compilan $ok · no $($tabla.Count - $ok - $to) · TIMEOUT $to"
