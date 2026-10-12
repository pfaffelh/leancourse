# sources -- the literature behind the course notes

Papers, theses and reports that a claim in the notes rests on, so that
a date or a wording can be checked later without searching for it
again.

## What is tracked and what is not

PDFs are **not** committed. `.gitignore` holds `/sources/*.pdf`,
because this repository is public: it is served at
<https://pfaffelh.github.io/leancourse/>, and committing a publisher's
PDF would republish it.

Tracked here are the index files -- [history-of-itp.md](history-of-itp.md)
and whatever comes after it -- with the full citation, a link, and one
line on what the item is good for.

A file that is genuinely free to redistribute (public domain, CC, or a
licence that says so) may go in anyway with `git add -f`. Note the
licence in the index when you do.

## Naming

`author-year-shorttitle.pdf`, lower case, no spaces:

    turing-1936-computable-numbers.pdf
    harrison-urban-wiedijk-2014-history-of-itp.pdf

## Adding something

One entry in the matching index file, in the same shape as the others:
citation, link, access, and a line saying which passage of the notes
uses it.
