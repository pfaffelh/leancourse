#!/usr/bin/env python3
"""Fetch the two company logos used in the 2026 section, with credits.

Both files are hosted on Wikimedia Commons under a free licence (the
marks themselves are below the threshold of originality).  They remain
registered trademarks of their owners; they are used here only to
identify who made the announcements described in the text, which is
nominative use and not an endorsement.
"""
import json, re, time, urllib.parse, urllib.request
from pathlib import Path

OUT = Path(__file__).resolve().parents[2] / "static" / "figures" / "logos"
UA = {"User-Agent": "leancourse-course-notes/1.0 (teaching material; https://github.com/pfaffelh/leancourse)"}
WANT = {
    "openai":    "File:OpenAI logo 2025 (wordmark).svg",
    "anthropic": "File:Anthropic logo.svg",
}
FREE = ("public domain", "cc0", "cc")

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
res = api({"action": "query", "format": "json", "prop": "imageinfo",
           "iiprop": "url|extmetadata", "iiurlwidth": "512",
           "titles": "|".join(WANT.values())})
by_title = {p["title"].replace("_", " "): p for p in res["query"]["pages"].values()}
rows = []
for slug, title in WANT.items():
    p = by_title.get(title.replace("_", " "))
    assert p and "imageinfo" in p, f"not found: {title}"
    ii = p["imageinfo"][0]; md = ii["extmetadata"]
    lic = md.get("LicenseShortName", {}).get("value", "?")
    assert lic.lower().startswith(FREE), f"{slug}: unexpected licence {lic}"
    author = " ".join(re.sub("<[^>]+>", " ", md.get("Artist", {}).get("value", "-")).split())
    # a PNG rendering: the manual embeds raster images everywhere else
    data = urllib.request.urlopen(urllib.request.Request(ii["thumburl"], headers=UA), timeout=60).read()
    (OUT / f"{slug}.png").write_bytes(data)
    rows.append((slug, author, lic, ii["descriptionurl"]))
    print(f"  {slug:10} {len(data)//1024:4d} kB  {lic:16} {author[:38]}")
    time.sleep(1.0)

with (OUT / "CREDITS.md").open("w") as f:
    f.write("# Logo credits\n\nBoth files come from Wikimedia Commons under the licence given.\n"
            "The marks are registered trademarks of their respective owners and are\n"
            "used here only to identify who made the announcements described in the\n"
            "text -- nominative use, not an endorsement.\n\n")
    for slug, author, lic, url in rows:
        f.write(f"- `{slug}.png` -- {author}, {lic}, via Wikimedia Commons, <{url}>\n")
print("wrote", OUT / "CREDITS.md")
