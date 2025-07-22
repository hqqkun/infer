import argparse
import sys
from pathlib import Path
import solver


def parse_arguments():
    parser = argparse.ArgumentParser(
        description="Program to process file path arguments"
    )
    parser.add_argument("-f", "--f", help="Input file path")
    args = parser.parse_args()

    if not args.f:
        print(
            "Error: You must specify a file path using the -f or --f argument",
            file=sys.stderr,
        )
        parser.print_help()
        sys.exit(1)

    return args.f


def validate_file_path(file_path_str):
    file_path = Path(file_path_str)

    if not file_path.exists():
        print(f"Error: File does not exist - {file_path}", file=sys.stderr)
        sys.exit(1)

    if not file_path.is_file():
        print(f"Error: Not a valid file - {file_path}", file=sys.stderr)
        sys.exit(1)

    return file_path


def read_file_content(file_path):
    try:
        with open(file_path, "r") as f:
            return f.read()
    except IOError as e:
        print(f"Error: Unable to read file - {e}", file=sys.stderr)
        sys.exit(1)


def process_with_solver(content):
    try:
        solver_instance = solver.MLIRSolver(model_str=content)
        if solver_instance.analyze() == solver.SolverStatus.SUCCESS:
            if solver_instance.is_satisfiable:
                print("Solution:", solver_instance.get_model())
            else:
                print("Constraints unsatisfiable")
    except Exception as e:
        import traceback

        print(f"Error: {str(e)}")
        # print traceback for debugging
        traceback.print_exc()


def main():
    file_path_str = parse_arguments()
    file_path = validate_file_path(file_path_str)
    file_content = read_file_content(file_path)
    process_with_solver(file_content)


if __name__ == "__main__":
    main()
