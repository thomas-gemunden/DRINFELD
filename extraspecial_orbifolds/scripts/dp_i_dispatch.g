# dp_i_dispatch.g — DP-I auto-dispatcher (issue #43, A-3b).
#
# Reads an A-3a `kernel.g` output for E_+(3), evaluates the predicate
# `kernel = 0` (i.e. kernel_size = 1, only the zero vec is in ker),
# persists a verdict record, and emits a JSON payload on stdout naming
# which downstream issues to unblock:
#
#   kernel = 0   (Tr is injective on H^3)  =>  branch: tier-3-cross-validation-only
#                Unblock: A-3d, A-5a. (A-3c skipped — no candidates to eliminate.)
#
#   kernel != 0  (Tr has non-trivial kernel) =>  branch: candidate-elimination
#                Unblock: A-3c, A-3d, A-5a.
#
# Verdict text format:  `DP-I: |ker Tr| = N. Next: <branch label>`.
#
# Usage (script form, defaults match A-3a's output path):
#   gap -q -b -c 'Read("dp_i_dispatch.g");'
# from extraspecial_orbifolds/scripts/.
#
# Usage (programmatic):
#   r := DispatchDPI("path/to/kernel.g", "path/to/verdict.g");
# Returns a record with fields kernel_size, kernel_trivial, branch_label,
# issues_to_unblock, verdict (the text), json (stdout payload).
#
# Setting DP_I_DISPATCH_NO_AUTOINVOKE before Read() suppresses the
# auto-invocation (used by the test suite).

# JSON-encode a list of strings as a JSON array (used for issues list).
_DPI_JsonStringList := function(strs)
    local parts;
    parts := List(strs, s -> Concatenation("\"", s, "\""));
    return Concatenation("[", JoinStringsWithSeparator(parts, ", "), "]");
end;;

# Local ternary helper, matching the idiom used elsewhere in scripts/.
If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# Write the verdict GAP source file with auto-wrapping disabled.
_DPI_WriteVerdict := function(path, src_path, ksize, ktrivial,
                              branch, issues, verdict)
    local stream;
    stream := OutputTextFile(path, false);
    Assert(0, stream <> fail,
           Concatenation("could not open ", path, " for writing"));
    SetPrintFormattingStatus(stream, false);
    PrintTo(stream,
        "# DP-I verdict from scripts/dp_i_dispatch.g (issue #43 A-3b).\n",
        "# Source kernel: ", src_path, "\n",
        "# Verdict: ", verdict, "\n",
        "return rec(\n",
        "    kernel_size       := ", ksize, ",\n",
        "    kernel_trivial    := ", ktrivial, ",\n",
        "    branch_label      := \"", branch, "\",\n",
        "    issues_to_unblock := ", issues, ",\n",
        "    verdict           := \"", verdict, "\"\n",
        ");;\n");
    CloseStream(stream);
end;;

DispatchDPI := function(kernel_path, verdict_path)
    local kernel_data, kernel_size, kernel_trivial, branch_label,
          issues_to_unblock, verdict_text, json, result;

    if not IsString(kernel_path) then
        Error("DispatchDPI: kernel_path must be a string");
    fi;
    if not IsString(verdict_path) then
        Error("DispatchDPI: verdict_path must be a string");
    fi;

    # The A-3a kernel.g is a GAP source file whose body returns a rec.
    kernel_data := ReadAsFunction(kernel_path)();
    Assert(0, IsRecord(kernel_data),
           Concatenation(kernel_path, " did not return a record"));
    Assert(0, IsBound(kernel_data.kernel_size),
           "kernel.g record missing kernel_size field");

    kernel_size := kernel_data.kernel_size;
    Assert(0, IsInt(kernel_size) and kernel_size >= 1,
           "kernel_size must be a positive integer");

    kernel_trivial := kernel_size = 1;
    if kernel_trivial then
        branch_label := "tier-3-cross-validation-only";
        issues_to_unblock := ["A-3d", "A-5a"];
    else
        branch_label := "candidate-elimination";
        issues_to_unblock := ["A-3c", "A-3d", "A-5a"];
    fi;

    verdict_text := Concatenation(
        "DP-I: |ker Tr| = ", String(kernel_size),
        ". Next: ", branch_label);

    # Hand-emit JSON (GAP has no standard JSON library; structure is
    # small enough that a literal Concatenation is clearer than a
    # general encoder).
    json := Concatenation(
        "{",
        "\"kernel_size\": ", String(kernel_size), ", ",
        "\"kernel_trivial\": ",
        If_(kernel_trivial, "true", "false"), ", ",
        "\"branch_label\": \"", branch_label, "\", ",
        "\"issues_to_unblock\": ", _DPI_JsonStringList(issues_to_unblock),
        "}");

    # Persist verdict as a GAP source file returning a record. Use an
    # OutputTextFile stream with PrintFormattingStatus disabled, because
    # the default PrintTo auto-wraps long lines at ~80 chars with a
    # backslash continuation, which silently breaks single-line comments.
    _DPI_WriteVerdict(verdict_path, kernel_path, kernel_size,
                      kernel_trivial, branch_label, issues_to_unblock,
                      verdict_text);

    # Stdout output.
    Print(verdict_text, "\n");
    Print("JSON: ", json, "\n");

    result := rec(
        kernel_size := kernel_size,
        kernel_trivial := kernel_trivial,
        branch_label := branch_label,
        issues_to_unblock := issues_to_unblock,
        verdict := verdict_text,
        json := json);
    return result;
end;;

# Auto-invoke when read as a script (guarded for the test suite).
if not IsBoundGlobal("DP_I_DISPATCH_NO_AUTOINVOKE") then
    DispatchDPI(
        "../../computed/transgression/3/kernel.g",
        "../../computed/transgression/3/dp_i_verdict.g");
fi;
