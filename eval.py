#!/usr/bin/env python3
import os
import sys
import shutil
import subprocess
from datetime import datetime
import argparse
from typing import Optional, Tuple, List, Dict

# --- Configuration ---
# Keep these in sync with benchmark.sh / benchmark-test.sh.
FULL_EXPERIMENTS = {
    "base": "-tycheck:no-refine=true",
    "syn": "-tycheck:infer-guard=false",
    "pre": "-tycheck:infer-guard=true -tycheck:use-syntactic-kill",
    "bool": "-tycheck:use-boolean-guard",
    "our": "",
    "prov": "-tycheck:infer-guard=true -tycheck:provenance",
}

TEST_EXPERIMENTS = {
    "base": "-tycheck:no-refine=true",
    "syn": "-tycheck:infer-guard=false",
    "nomut": "-tycheck:infer-guard=true -tycheck:use-syntactic-kill",
    "bool": "-tycheck:use-boolean-guard",
    "our": "",
    "prov": "-tycheck:infer-guard=true -tycheck:provenance",
}

# --- Rich Library Check ---
try:
    from rich.console import Console
    from rich.progress import Progress, BarColumn, TextColumn, TimeElapsedColumn
except ImportError:
    Console = None  # type: ignore[assignment]
    Progress = None  # type: ignore[assignment]
    BarColumn = None  # type: ignore[assignment]
    TextColumn = None  # type: ignore[assignment]
    TimeElapsedColumn = None  # type: ignore[assignment]

# --- Global Setup ---
class _SimpleConsole:
    def __init__(self):
        self._records: List[str] = []

    def log(self, message: str) -> None:
        line = f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {message}"
        self._records.append(line)
        print(line)

    def print(self, message: str) -> None:
        self._records.append(str(message))
        print(message)

    def save_text(self, path: str) -> None:
        with open(path, "w", encoding="utf-8") as f:
            f.write("\n".join(self._records))
            f.write("\n")


console = Console(record=True) if Console else _SimpleConsole()
LOG_FILE = "log.py.txt"

# --- Core Functions ---

def log(message: str):
    """Logs a message to the console and the global log file."""
    console.log(message)
    with open(LOG_FILE, "a") as f:
        # Strip rich's markup for the plain text log file
        f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {message}\n")

def initdir(dirname: str):
    """Deletes and recreates a directory to ensure it's empty."""
    if os.path.exists(dirname):
        shutil.rmtree(dirname)
    os.makedirs(dirname)

def run_command(command: str, quiet: bool = False):
    """
    Runs a shell command, logging its execution and output.
    In quiet mode, stdout/stderr are redirected to the log file instead of the console.
    """
    log(f"Executing: {command}")
    
    # Using shell=True for direct translation of shell script commands
    # This inherits the shell environment, including ESMETA_HOME
    process = subprocess.run(
        command,
        shell=True,
        capture_output=True,
        text=True,
    )

    log_output = f"--- stdout ---\n{process.stdout}\n--- stderr ---\n{process.stderr}\n"
    
    with open(LOG_FILE, "a") as f:
        f.write(log_output)

    if not quiet:
        if process.stdout:
            console.print(process.stdout)
        if process.stderr:
            if Console:
                console.print(f"[red]{process.stderr}[/red]")
            else:
                console.print(process.stderr)
    
    return process

def doit(dirname: str, option: str, versions: List[str]):
    """
    Runs a single experiment configuration.
    This involves creating a directory, iterating through versions,
    running the analysis, and summarizing the results.
    """
    initdir(dirname)
    original_cwd = os.getcwd()
    os.chdir(dirname)

    # Create the header for the summary file
    head = "\t".join([
        "#", "version", "iter", "duration (ms)", "# errors",
        "# analyzed funcs", "# total funcs", "# analyzed nodes", "# total nodes",
        "# refined targets", "# refined locals", "# avg. depth", "# guards",
        "# total provenances", "# avg. prov size", "# avg. prov depth", "# avg. prov leaf"
    ])
    run_command(f"echo '{head}' > summary.tsv")

    log(f"Starting experiment '{dirname}' on {len(versions)} versions...")

    def _one(version_idx: int, version: str) -> None:
        esmeta_cmd = f"esmeta tycheck -tycheck:detail-log -extract:target={version} {option}"
        run_command(esmeta_cmd, quiet=True)

        # $ESMETA_HOME should be available in the shell environment
        run_command(f"mv $ESMETA_HOME/logs/analyze {version_idx}", quiet=True)

        # Append results to summary.tsv
        summary_line = f"'{version_idx}\t{version}\t'"
        run_command(f"echo -n {summary_line} >> summary.tsv", quiet=True)
        run_command(f"cat {version_idx}/summary >> summary.tsv", quiet=True)
        run_command("echo '' >> summary.tsv", quiet=True)

    # Set up and run the progress bar (if available)
    if Progress:
        with Progress(
            TextColumn("[progress.description]{task.description}"),
            BarColumn(),
            TextColumn("[progress.percentage]{task.percentage:>3.0f}%"),
            TimeElapsedColumn(),
            console=console,  # type: ignore[arg-type]
        ) as progress:
            task = progress.add_task(f"[cyan]Running {dirname}...", total=len(versions))
            for i, version in enumerate(versions):
                _one(i, version)
                progress.update(task, advance=1, description=f"[cyan]{dirname}: {version[:30]:<30}")
    else:
        for i, version in enumerate(versions):
            console.log(f"{dirname}: {i+1}/{len(versions)} {version}")
            _one(i, version)

    log(f"Finished experiment '{dirname}'.")
    os.chdir(original_cwd)

# --- Main Execution ---

def _read_versions(path: str) -> List[str]:
    try:
        with open(path) as f:
            return [line.strip() for line in f if line.strip()]
    except FileNotFoundError:
        console.print(f"[red]Error: versions file not found: {path}[/red]")
        return []


def _resolve_experiment(experiment: str, experiments: Dict[str, str]) -> Optional[Tuple[str, str]]:
    if experiment in experiments:
        return experiment, experiments[experiment]

    aliases = {
        "boolean": "bool",
        "pre": "nomut",
        "nomut": "pre",
    }
    canonical = aliases.get(experiment)
    if canonical and canonical in experiments:
        return canonical, experiments[canonical]
    return None


def main():
    """
    Parses command-line arguments and runs the appropriate experiments.
    """
    parser = argparse.ArgumentParser(
        description="Run ESMETA evaluation experiments with a rich progress bar.",
        formatter_class=argparse.RawTextHelpFormatter
    )
    parser.add_argument(
        "experiment",
        nargs="?",  # Makes the argument optional
        default=None,
        help=(
            "Optional: Name of a single experiment to run. If not provided, all experiments will be run.\n"
            "Full mode: base syn pre bool our prov\n"
            "Test mode (--test): base syn nomut bool our prov\n"
            "Aliases: boolean->bool, pre<->nomut"
        ),
    )
    parser.add_argument(
        "--test",
        action="store_true",
        help="Run the quick test benchmark (uses versions-test and nomut), matching benchmark-test.sh.",
    )
    args = parser.parse_args()

    # Change to the script's directory to resolve paths correctly
    script_dir = os.path.dirname(os.path.realpath(__file__))
    os.chdir(script_dir)

    experiments = TEST_EXPERIMENTS if args.test else FULL_EXPERIMENTS
    versions_file = "versions-test" if args.test else "versions"
    versions = _read_versions(versions_file)
    if not versions:
        return

    if args.experiment:
        # --- Run a single experiment ---
        resolved = _resolve_experiment(args.experiment, experiments)
        if not resolved:
            console.print(
                f"[red]Error: Unknown experiment '{args.experiment}' for this mode.[/red]\n"
                f"Available: {' '.join(experiments.keys())}"
            )
            return
        target_experiment, option = resolved
        log(f"Running single experiment: {target_experiment} (from: {args.experiment})")
        
        if not os.path.exists("result"):
            os.makedirs("result")
        
        original_cwd = os.getcwd()
        os.chdir("result")
        doit(target_experiment, option, versions)
        os.chdir(original_cwd)
    else:
        # --- Run all experiments ---
        log("Running all experiments")
        initdir("result")
        
        original_cwd = os.getcwd()
        os.chdir("result")
        for name, option in experiments.items():
            doit(name, option, versions)
        os.chdir(original_cwd)

    log("All tasks complete.")
    # Save the full console output to a file
    console.save_text(os.path.join(script_dir, "console_output.txt"))


if __name__ == "__main__":
    main()
