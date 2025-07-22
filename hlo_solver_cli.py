import sys
from pathlib import Path
import hydra
from hydra.core.global_hydra import GlobalHydra
from omegaconf import DictConfig, OmegaConf
from stablehlo_solver import solver


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


def process_with_solver(content, cfg):
    try:
        solver_instance = solver.MLIRSolver(
            model_str=content, **OmegaConf.to_container(cfg.solver, resolve=True)
        )
        if solver_instance.analyze() == solver.SolverStatus.SUCCESS:
            if solver_instance.is_satisfiable:
                print("Solution:", solver_instance.get_model())
            else:
                print("Constraints unsatisfiable")
    except Exception as e:
        import traceback

        print(f"Error: {str(e)}")
        traceback.print_exc()


@hydra.main(version_base=None, config_path="conf", config_name="config")
def main(cfg: DictConfig):
    if not cfg.file_path:
        print("Error: You must specify a file path in the config", file=sys.stderr)
        sys.exit(1)

    file_path = validate_file_path(cfg.file_path)
    file_content = read_file_content(file_path)
    process_with_solver(file_content, cfg)


if __name__ == "__main__":
    main()
