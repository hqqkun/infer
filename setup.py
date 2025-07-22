from setuptools import setup, Extension
from Cython.Build import cythonize

ext_modules = [
    Extension(
        "stablehlo_solver",
        sources=[
            "stablehlo_solver/__init__.py",
            "stablehlo_solver/solver.py",
            "stablehlo_solver/op_visitor.py",
        ],
        extra_compile_args=["-O3"],
    )
]

# 明确指定语言级别，确保生成正确的初始化函数
setup(
    name="stablehlo_solver",
    ext_modules=cythonize(ext_modules, language_level="3"),
)
