#!/usr/bin/env bash
#
# Copies the libkeccaktree-* artifacts of a "Build & Test" run into lib/, so a
# pull request that changes src/ can carry matching libraries and its Go
# binding tests pass. After the merge, "Update Static Libraries" rebuilds and
# attests them on main.
#
#   .github/scripts/fetch-ci-libs.sh            # latest run on the current branch
#   .github/scripts/fetch-ci-libs.sh <run-id>   # a specific run
#
# Start a run on your branch first (Actions > Build & Test > Run workflow, or
# `gh workflow run build.yml --ref <branch>`). Needs the GitHub CLI.

set -euo pipefail
cd "$(cd "$(dirname "$0")/../.." && pwd)"

run_id="${1:-}"
if [ -z "$run_id" ]; then
	branch="$(git rev-parse --abbrev-ref HEAD)"
	run_id="$(gh run list --workflow build.yml --branch "$branch" --status success \
		--limit 1 --json databaseId --jq '.[0].databaseId')"
	[ -n "$run_id" ] || { echo "no successful Build & Test run on $branch" >&2; exit 1; }
fi

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
gh run download "$run_id" -p 'libkeccaktree-*' -D "$tmp"

for platform in linux_amd64 linux_arm64 linux_riscv64 darwin_arm64 windows_amd64; do
	art="$tmp/libkeccaktree-${platform//_/-}"
	(cd "$art" && sha256sum -c libkeccaktree.a.sha256 >/dev/null)
	cp "$art/libkeccaktree.a" "$art/libkeccaktree.a.sha256" "$art/libkeccaktree.a.buildinfo" "lib/$platform/"
done
git rev-parse HEAD > lib/SOURCE_COMMIT
echo "lib/ updated from run $run_id ($(git rev-parse --short HEAD)); commit it with your change"
