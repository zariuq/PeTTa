#!/usr/bin/env -S LC_ALL=C LC_NUMERIC=C awk -f
#
# Usage:
#   tests/tools/summarize_he_translation_budget.awk [BENCH.tsv]
#   tests/tools/summarize_he_translation_budget.awk -v lane=preserve_hyperpose [BENCH.tsv]
#   tests/tools/summarize_he_translation_budget.awk -v n=20 [BENCH.tsv]
#
# Reads he_translation_bench.tsv and reports wall-time budget margins.
# The shebang forces C numeric parsing/formatting for dot-decimal TSV values.

BEGIN {
    FS = OFS = "\t"
    if (ARGC == 1) {
        ARGV[1] = ".he-logs/he_translation_bench.tsv"
        ARGC = 2
    }
    if (lane == "") lane = "pure_portable"
    if (lane == "portable" || lane == "pure") lane = "pure_portable"
    if (lane == "parallel" || lane == "hyperpose") lane = "preserve_hyperpose"
    if (n == "" || n + 0 <= 0) n = 12
    if (ratio_limit == "") ratio_limit = 2.23
    if (startup_allowance == "") startup_allowance = 0.25
}

function is_number(value) {
    return value != "" && value != "NA" && value != "-" &&
           value ~ /^-?[0-9]+([.][0-9]+)?$/
}

function budget_for(base_wall) {
    if (!is_number(base_wall) || base_wall + 0 <= 0) return "NA"
    return sprintf("%.3f", (base_wall * ratio_limit) + startup_allowance)
}

function need(name) {
    if (!(name in col)) {
        missing[name] = 1
        header_bad = 1
        return 0
    }
    return col[name]
}

function remember_margin(source, category, status, base_wall, he_wall, budget_wall,
                         ratio_wall, margin_wall) {
    margin_rows++
    margin_source[margin_rows] = source
    margin_category[margin_rows] = category
    margin_status[margin_rows] = status
    margin_base[margin_rows] = base_wall + 0
    margin_he[margin_rows] = he_wall + 0
    margin_budget[margin_rows] = budget_wall + 0
    margin_ratio[margin_rows] = ratio_wall + 0
    margin_value[margin_rows] = margin_wall + 0

    if (margin_rows == 1 || margin_wall + 0 < min_margin) {
        min_margin = margin_wall + 0
        min_source = source
    }
    if (margin_rows == 1 || margin_wall + 0 > max_margin) {
        max_margin = margin_wall + 0
        max_source = source
    }
}

function remember_faster(source, category, status, base_wall, he_wall, budget_wall,
                         ratio_wall) {
    faster_rows++
    faster_source[faster_rows] = source
    faster_category[faster_rows] = category
    faster_status[faster_rows] = status
    faster_base[faster_rows] = base_wall + 0
    faster_he[faster_rows] = he_wall + 0
    faster_budget[faster_rows] = budget_wall + 0
    faster_ratio[faster_rows] = ratio_wall + 0
    faster_delta[faster_rows] = (he_wall + 0) - (base_wall + 0)
}

function sort_by_margin(    i, j, tmp) {
    for (i = 1; i <= margin_rows; i++) margin_order[i] = i
    for (i = 1; i <= margin_rows; i++) {
        for (j = i + 1; j <= margin_rows; j++) {
            if (margin_value[margin_order[j]] < margin_value[margin_order[i]]) {
                tmp = margin_order[i]
                margin_order[i] = margin_order[j]
                margin_order[j] = tmp
            }
        }
    }
}

function sort_by_faster_delta(    i, j, tmp) {
    for (i = 1; i <= faster_rows; i++) faster_order[i] = i
    for (i = 1; i <= faster_rows; i++) {
        for (j = i + 1; j <= faster_rows; j++) {
            if (faster_delta[faster_order[j]] < faster_delta[faster_order[i]]) {
                tmp = faster_order[i]
                faster_order[i] = faster_order[j]
                faster_order[j] = tmp
            }
        }
    }
}

FNR == 1 {
    for (i = 1; i <= NF; i++) col[$i] = i

    source_col = need("source")
    base_col = need("default_wall")
    if (lane == "pure_portable") {
        he_col = need("pure_portable_wall")
        ratio_col = need("pure_portable_ratio_wall")
        category_col = need("pure_portable_category")
        budget_col = need("pure_portable_perf_budget_wall")
        status_col = need("pure_portable_perf_budget_status")
    } else if (lane == "preserve_hyperpose") {
        he_col = need("preserve_hyperpose_wall")
        ratio_col = need("preserve_hyperpose_ratio_wall")
        category_col = need("preserve_hyperpose_category")
        budget_col = need("preserve_hyperpose_perf_budget_wall")
        status_col = need("preserve_hyperpose_perf_budget_status")
    } else {
        printf "unknown lane: %s\n", lane > "/dev/stderr"
        header_bad = 1
    }
    if (header_bad) {
        for (name in missing) {
            printf "missing required column: %s\n", name > "/dev/stderr"
        }
        exit 65
    }
    next
}

{
    row_count++
    source = $source_col
    base_wall = $base_col
    he_wall = $he_col
    ratio_wall = $ratio_col
    category = $category_col
    budget_wall = $budget_col
    status = $status_col

    if (status == "" || status == "-") status = "unknown"
    status_count[status]++

    if (!is_number(budget_wall)) budget_wall = budget_for(base_wall)
    if (is_number(base_wall) && is_number(he_wall)) {
        if (!is_number(ratio_wall)) {
            ratio_wall = (base_wall + 0 > 0) ? sprintf("%.3f", (he_wall + 0) / (base_wall + 0)) : "NA"
        }
        if (he_wall + 0 < base_wall + 0) {
            remember_faster(source, category, status, base_wall, he_wall,
                            budget_wall, ratio_wall)
        }
    }
    if (is_number(he_wall) && is_number(budget_wall)) {
        margin_wall = (budget_wall + 0) - (he_wall + 0)
        remember_margin(source, category, status, base_wall, he_wall,
                        budget_wall, ratio_wall, margin_wall)
        if (margin_wall + 0 < -0.0005) computed_gaps++
    } else {
        unknown_margin_rows++
    }
}

END {
    if (header_bad) exit 65
    print "# HE translation performance budget margins"
    print "metric", "value"
    print "lane", lane
    print "formula", sprintf("he_wall <= default_wall * %.6g + %.6gs",
                             ratio_limit, startup_allowance)
    print "rows", row_count + 0
    print "status_ok", status_count["ok"] + 0
    print "status_gap", status_count["gap"] + 0
    print "status_unknown", status_count["unknown"] + 0
    print "rows_with_margin", margin_rows + 0
    print "rows_without_margin", unknown_margin_rows + 0
    print "computed_gap_margins", computed_gaps + 0
    if (margin_rows > 0) {
        print "min_margin_seconds", sprintf("%.3f", min_margin)
        print "min_margin_source", min_source
        print "max_margin_seconds", sprintf("%.3f", max_margin)
        print "max_margin_source", max_source
    }
    print "faster_than_native", faster_rows + 0

    if (margin_rows > 0) {
        sort_by_margin()
        print ""
        print "# tightest_margins"
        print "source", "default_wall", "he_wall", "budget_wall",
              "margin_wall", "ratio_wall", "status", "category"
        limit = (n + 0 < margin_rows) ? n + 0 : margin_rows
        for (rank = 1; rank <= limit; rank++) {
            idx = margin_order[rank]
            print margin_source[idx],
                  sprintf("%.3f", margin_base[idx]),
                  sprintf("%.3f", margin_he[idx]),
                  sprintf("%.3f", margin_budget[idx]),
                  sprintf("%.3f", margin_value[idx]),
                  sprintf("%.3f", margin_ratio[idx]),
                  margin_status[idx],
                  margin_category[idx]
        }
    }

    if (faster_rows > 0) {
        sort_by_faster_delta()
        print ""
        print "# faster_than_native"
        print "source", "default_wall", "he_wall", "delta_wall",
              "budget_wall", "ratio_wall", "status", "category"
        limit = (n + 0 < faster_rows) ? n + 0 : faster_rows
        for (rank = 1; rank <= limit; rank++) {
            idx = faster_order[rank]
            print faster_source[idx],
                  sprintf("%.3f", faster_base[idx]),
                  sprintf("%.3f", faster_he[idx]),
                  sprintf("%.3f", faster_delta[idx]),
                  sprintf("%.3f", faster_budget[idx]),
                  sprintf("%.3f", faster_ratio[idx]),
                  faster_status[idx],
                  faster_category[idx]
        }
    }
}
