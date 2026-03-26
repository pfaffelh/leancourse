import Leancourse
import Manual.Meta

open Verso.Genre Manual
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Verso.Output.Html in
def searchModule := {{
    <script type="module" src="/static/search/search-init.js"></script>
  }}

open Verso.Output.Html in
def staticCss := {{
    <link rel="stylesheet" href="/static/colors.css" />
    <link rel="stylesheet" href="/static/theme.css" />
    <link rel="stylesheet" href="/static/print.css" />
    <link rel="stylesheet" href="/static/search/search-box.css" />
    <link rel="stylesheet" href="/static/fonts/source-serif/source-serif-text.css" />
    <link rel="stylesheet" href="/static/fonts/source-code-pro/source-code-pro.css" />
    <link rel="stylesheet" href="/static/katex/katex.min.css" />
  }}

open Verso.Output.Html in
def staticJs := {{
    <script src="/static/katex/katex.min.js"></script>
    <script src="/static/math.js"></script>
    <script src="/static/search/fuzzysort.js"></script>
    <script src="/static/print.js"></script>
  }}

def KaTeXLicense : LicenseInfo where
  identifier := "MIT"
  dependency := "KaTeX"
  howUsed := "KaTeX is used to render mathematical notation."
  link := "https://katex.org/"
  text := #[(some "The MIT License", text)]
where
  text := r#"
Copyright (c) 2013-2020 Khan Academy and other contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"#

def main :=
  manualMain (%doc Leancourse) (config := config)
where
  config := {
    extraFiles := [("static", "static")],
    extraHead := #[searchModule, staticCss, staticJs],
    emitTeX := false,
    emitHtmlSingle := .immediately,
    emitHtmlMulti := .immediately,
    logo := some "/static/lean_logo.svg",
    sourceLink := some "https://github.com/pfaffelh/leancourse",
    issueLink := some "https://github.com/pfaffelh/leancourse/issues",
  }
