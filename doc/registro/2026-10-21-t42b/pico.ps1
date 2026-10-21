# pico.ps1 NOMBRE — sigue el proceso NOMBRE (el primero que haya) y, cuando termina, imprime su pico de memoria y su CPU
param([string]$Nombre = 'leanchecker')
$p = $null
for ($i = 0; $i -lt 120 -and -not $p; $i++) { $p = Get-Process -Name $Nombre -ErrorAction SilentlyContinue | Select-Object -First 1; if (-not $p) { Start-Sleep -Milliseconds 500 } }
if (-not $p) { "no hay proceso $Nombre"; exit 1 }
$pico = 0; $cpu = 0; $t0 = $p.StartTime
while (-not $p.HasExited) {
  try { $p.Refresh(); if ($p.PeakWorkingSet64 -gt $pico) { $pico = $p.PeakWorkingSet64 }; $cpu = $p.TotalProcessorTime.TotalSeconds } catch {}
  Start-Sleep -Seconds 2
}
"{0} (pid {1}) terminó: pico de memoria {2} MB; CPU {3} s; de {4:HH:mm:ss} a {5:HH:mm:ss}" -f $Nombre, $p.Id, [int]($pico / 1MB), [int]$cpu, $t0, (Get-Date)
