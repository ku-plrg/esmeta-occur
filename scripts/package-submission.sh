#!/usr/bin/env bash
# Build clean, anonymized copies of the artifact and the supplementary material
# from the committed state (HEAD) of this repository. Maintainers only; this
# script is not included in the packaged artifact.
#
#   scripts/package-submission.sh [out-dir]     (default: submission)
#
# The repository is self-contained: the supplementary report is tracked as
# tech-report.pdf at the top level (rebuild it from the paper repository and
# commit it whenever the report changes). The same file goes into the artifact
# and into the supplementary zip (as report.pdf).
#
# Outputs:
#   <out-dir>/artifact/          a fresh git repository (one anonymous commit,
#                                ecma262 registered as a pinned submodule)
#                                ready to push for anonymous.4open.science
#   <out-dir>/supplementary.zip  proof/ and report.pdf (= tech-report.pdf) for HotCRP
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
cd "$ROOT"
OUT=${1:-submission}
ART="$OUT/artifact"

if ! git cat-file -e HEAD:tech-report.pdf 2>/dev/null; then
  echo "error: tech-report.pdf is not committed" >&2; exit 1
fi
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "warning: uncommitted changes are NOT included (packaging HEAD)" >&2
fi

rm -rf "$ART" "$OUT/supplementary.zip"
mkdir -p "$ART"
git archive HEAD | tar -x -C "$ART"

# --- files that must not be in the submission ---------------------------------
rm -rf "$ART/.github" "$ART/.completion" "$ART/scripts/package-submission.sh" \
  "$ART/scripts/.anon-patterns"
# keep README.md (any directory) and LICENSE.md; drop every other Markdown file
find "$ART" -name '*.md' ! -name README.md ! -name LICENSE.md -delete
# drop maintainer-only sections of README files
find "$ART" -name README.md -exec \
  sed -i.bak '/<!-- BEGIN MAINTAINERS -->/,/<!-- END MAINTAINERS -->/d' {} \;
find "$ART" -name '*.bak' -delete

# --- anonymization check ------------------------------------------------------
# Identifying strings: one extended regex per line in scripts/.anon-patterns
# (removed from the packaged artifact like this script).
PATTERN_FILE="$ROOT/scripts/.anon-patterns"
if [ ! -f "$PATTERN_FILE" ]; then
  echo "error: $PATTERN_FILE not found (one identifying regex per line)" >&2; exit 1
fi
TEXT_PATTERNS=$(grep -v '^[[:space:]]*$' "$PATTERN_FILE" | paste -sd'|' -)
if grep -rIniE "$TEXT_PATTERNS" "$ART" >/dev/null; then
  echo "error: identifying strings found:" >&2
  grep -rIniE "$TEXT_PATTERNS" "$ART" | head -20 >&2
  exit 1
fi
if command -v pdftotext >/dev/null; then
  # check the text before the references (third-person self-citations are allowed)
  if pdftotext "$ART/tech-report.pdf" - | awk '/^References$/{exit} {print}' \
     | grep -iE "$TEXT_PATTERNS" >/dev/null; then
    echo "error: identifying strings found in tech-report.pdf" >&2; exit 1
  fi
else
  echo "warning: pdftotext not found; tech-report.pdf is not checked" >&2
fi

# --- fresh repository with the pinned ecma262 submodule ------------------------
SUB_URL=$(git config -f .gitmodules submodule.ecma262.url)
SUB_REV=$(git ls-tree HEAD ecma262 | awk '{print $3}')
(
  cd "$ART"
  rmdir ecma262 2>/dev/null || true
  git init -q
  git add -A
  # register the submodule without cloning it (pinned to the evaluated commit)
  git update-index --add --cacheinfo "160000,$SUB_REV,ecma262"
  GIT_AUTHOR_NAME=Anonymous GIT_AUTHOR_EMAIL=anonymous@example.com \
  GIT_COMMITTER_NAME=Anonymous GIT_COMMITTER_EMAIL=anonymous@example.com \
    git commit -q -m "Artifact"
)

# --- supplementary material ---------------------------------------------------
TMP=$(mktemp -d)
cp -r "$ART/proof" "$TMP/proof"
cp "$ART/tech-report.pdf" "$TMP/report.pdf"
(cd "$TMP" && zip -qr - .) > "$OUT/supplementary.zip"
rm -rf "$TMP"

cat <<MSG
artifact      : $ART  (ecma262 -> $SUB_URL @ ${SUB_REV:0:9})
supplementary : $OUT/supplementary.zip
To publish the artifact:
  cd $ART && git remote add origin <new-repository-url> && git push -u origin HEAD:main
then create an anonymized link of that repository at https://anonymous.4open.science
MSG
