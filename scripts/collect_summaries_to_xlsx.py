#!/usr/bin/env python3

import argparse
import csv
import math
import sys
from pathlib import Path


SUMMARY_DIRS_DEFAULT = ["base", "syn", "nomut", "bool", "our", "prov"]


def _coerce_cell(raw: str):
    s = raw.strip()
    if s == "":
        return None
    if s.lower() == "nan":
        return None
    try:
        return int(s)
    except ValueError:
        pass
    try:
        value = float(s)
        if math.isnan(value):
            return None
        return value
    except ValueError:
        return s


def _read_tsv_rows(path: Path) -> list[list[str]]:
    with path.open("r", encoding="utf-8", newline="") as f:
        return list(csv.reader(f, delimiter="\t"))


def _autosize_columns(worksheet, col_widths: list[int]) -> None:
    # Excel column width is roughly "number of characters"; add a bit of padding.
    for col, width in enumerate(col_widths):
        worksheet.set_column(col, col, min(max(width + 2, 8), 80))


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Collect result/*/summary.tsv into a single XLSX workbook (one sheet per TSV)."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root (default: inferred from this script location).",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output XLSX path (default: <root>/result/summary.xlsx).",
    )
    parser.add_argument(
        "--dirs",
        nargs="+",
        default=SUMMARY_DIRS_DEFAULT,
        help=f"Result directories to include (default: {' '.join(SUMMARY_DIRS_DEFAULT)}).",
    )
    args = parser.parse_args()

    root: Path = args.root.resolve()
    out_path: Path = (args.out or (root / "result" / "summary.xlsx")).resolve()

    try:
        import xlsxwriter  # type: ignore
    except ModuleNotFoundError:
        print(
            "Missing dependency: XlsxWriter\n"
            "Install it with:\n"
            "  python3 -m pip install -r scripts/requirements-excel.txt",
            file=sys.stderr,
        )
        return 2

    summaries: list[tuple[str, Path]] = []
    for d in args.dirs:
        tsv_path = root / "result" / d / "summary.tsv"
        if not tsv_path.is_file():
            print(f"Missing input TSV: {tsv_path}", file=sys.stderr)
            return 2
        summaries.append((d, tsv_path))

    out_path.parent.mkdir(parents=True, exist_ok=True)
    workbook = xlsxwriter.Workbook(out_path)
    header_fmt = workbook.add_format({"bold": True, "bg_color": "#F2F2F2"})

    for sheet_name, tsv_path in summaries:
        rows = _read_tsv_rows(tsv_path)
        if not rows:
            workbook.add_worksheet(sheet_name)
            continue

        expected_cols = max(len(r) for r in rows)
        worksheet = workbook.add_worksheet(sheet_name[:31])
        worksheet.freeze_panes(1, 0)

        col_widths = [0] * expected_cols
        for r_idx, row in enumerate(rows):
            if len(row) < expected_cols:
                row = row + [""] * (expected_cols - len(row))

            for c_idx, cell in enumerate(row):
                value = _coerce_cell(cell) if r_idx > 0 else cell
                if value is None:
                    worksheet.write_blank(r_idx, c_idx, None)
                elif r_idx == 0:
                    worksheet.write(r_idx, c_idx, value, header_fmt)
                else:
                    worksheet.write(r_idx, c_idx, value)

                display = "" if value is None else str(value)
                col_widths[c_idx] = max(col_widths[c_idx], len(display))

        if len(rows) >= 2 and expected_cols >= 1:
            worksheet.autofilter(0, 0, len(rows) - 1, expected_cols - 1)
        _autosize_columns(worksheet, col_widths)

    workbook.close()
    print(f"Wrote: {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

