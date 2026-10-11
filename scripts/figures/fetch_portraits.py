#!/usr/bin/env python3
"""Fetch the researcher portraits from Wikimedia Commons, with credits.

Every file is reproduced unchanged under its own licence; the credits
written to CREDITS.md must be reproduced wherever the images are shown.
Only files hosted on Commons under a CC licence are taken.
"""
import json, re, time, urllib.parse, urllib.request
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / "static" / "figures" / "portraits"
UA = {"User-Agent": "leancourse-course-notes/1.0 (teaching material; https://github.com/pfaffelh/leancourse)"}
WANT = {                       # slug -> Commons file
    "hales":     "File:Halescropped.jpg",
    "scholze":   "File:Peter Scholze 2014 cropped.jpg",
    "buzzard":   "File:Kevin buzzard in 2007.jpg",
    "demoura":   "File:Leo de Moura P1210629.jpg",
    "viazovska": "File:Maryna Vazovska MFO 2013 crop.jpg",
    "gowers":    "File:William Timothy Gowers Oslo 2012.jpg",
    "green":     "File:Ben Green.jpg",
    "tao":       "File:Terence Tao at IPAM's Fireside Chat 2026 (50m16s) (cropped).jpg",
}

def api(params, tries=5):
    url = "https://commons.wikimedia.org/w/api.php?" + urllib.parse.urlencode(params)
    for i in range(tries):
        try:
            return json.load(urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=40))
        except urllib.error.HTTPError as e:
            if e.code == 429:
                time.sleep(15 * (i + 1)); continue
            raise
    raise RuntimeError("rate limited")

OUT.mkdir(parents=True, exist_ok=True)
res = api({"action":"query","format":"json","prop":"imageinfo",
           "iiprop":"url|extmetadata","iiurlwidth":"600",
           "titles":"|".join(WANT.values())})
by_title = {p["title"].replace("_", " "): p for p in res["query"]["pages"].values()}
rows = []
for slug, title in WANT.items():
    p = by_title.get(title.replace("_", " "))
    assert p and "imageinfo" in p, f"not found: {title}"
    ii = p["imageinfo"][0]; md = ii["extmetadata"]
    lic = md.get("LicenseShortName", {}).get("value", "?")
    assert lic.lower().startswith("cc"), f"{slug}: unexpected licence {lic}"
    author = " ".join(re.sub("<[^>]+>", " ", md.get("Artist", {}).get("value", "?")).split())
    data = urllib.request.urlopen(urllib.request.Request(ii["thumburl"], headers=UA), timeout=60).read()
    (OUT / f"{slug}.jpg").write_bytes(data)
    rows.append((slug, author, lic, ii["descriptionurl"]))
    print(f"  {slug:10} {len(data)//1024:4d} kB  {lic:16} {author[:38]}")
    time.sleep(1.0)

with (OUT / "CREDITS.md").open("w") as f:
    f.write("# Portrait credits\n\nAll images are from Wikimedia Commons and are reproduced\n"
            "unchanged under the licence given. The attribution below must be\n"
            "reproduced wherever the images are shown.\n\n")
    for slug, author, lic, url in rows:
        f.write(f"- `{slug}.jpg` -- {author}, {lic}, via Wikimedia Commons, <{url}>\n")
print("wrote", OUT / "CREDITS.md")
