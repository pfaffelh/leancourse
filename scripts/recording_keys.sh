#!/usr/bin/env bash
# F1/F2/F3 switch OBS between camera, slides and VS Code while recording;
# F7 pauses, F8 resumes, F9 starts and F10 stops the recording.
#
#   scripts/recording_keys.sh on     F1-F3 and F7-F10 to OBS
#   scripts/recording_keys.sh off    give them back to the applications
#
# The keys are GNOME custom shortcuts, not OBS hotkeys: on Linux an OBS
# hotkey also reaches the focused window, and F1/F2/F3 mean command
# palette, rename and find-next in VS Code; F7 asks about caret browsing
# in Chrome, F8 jumps to the next problem in VS Code. A GNOME shortcut
# swallows the key. While "on", these keys therefore do nothing else
# anywhere -- turn it off after recording.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
schema=org.gnome.settings-daemon.plugins.media-keys
base=/org/gnome/settings-daemon/plugins/media-keys/custom-keybindings
ids=(obs-f1 obs-f2 obs-f3 obs-f7 obs-f8 obs-f9 obs-f10)
keys=(F1 F2 F3 F7 F8 F9 F10)
args=(camera slides code pause resume start stop)
names=("OBS: Kamera" "OBS: Folien" "OBS: VS Code" "OBS: Pause"
       "OBS: Weiter" "OBS: Aufnahme starten" "OBS: Aufnahme beenden")

current=$(gsettings get $schema custom-keybindings)
# drop our three paths from the list, keep everyone else's
others=$(python3 -c '
import ast, sys
cur = sys.argv[1].replace("@as ", "")
lst = ast.literal_eval(cur) if cur.strip() else []
print(repr([p for p in lst if "/obs-f" not in p]))' "$current")

case "${1:-}" in
  on)
    new=$(python3 -c '
import ast, sys
print(repr(ast.literal_eval(sys.argv[1]) + [p + "/" for p in sys.argv[2:]]))' \
      "$others" "${ids[@]/#/$base/}")
    for i in "${!ids[@]}"; do
      p="$base/${ids[$i]}/"
      gsettings set "$schema.custom-keybinding:$p" name "${names[$i]}"
      gsettings set "$schema.custom-keybinding:$p" command "python3 $here/obs_scene.py ${args[$i]}"
      gsettings set "$schema.custom-keybinding:$p" binding "${keys[$i]}"
    done
    gsettings set $schema custom-keybindings "$new"
    echo "F1 camera, F2 slides, F3 VS Code, F7 pause, F8 resume, F9 start, F10 stop -- on. Turn off with: $0 off"
    ;;
  off)
    gsettings set $schema custom-keybindings "$others"
    for id in "${ids[@]}"; do
      gsettings reset-recursively "$schema.custom-keybinding:$base/$id/" 2>/dev/null || true
    done
    echo "F1-F3 and F7-F10 back to the applications."
    ;;
  *)
    echo "usage: $0 on|off" >&2; exit 2 ;;
esac
