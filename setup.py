from setuptools import setup, Extension
from Cython.Build import cythonize

ext_modules = [
    Extension(
        "infer_inputs_ext",  # 模块名必须与导入时一致
        sources=[
            "infer_inputs/__init__.py",
            "infer_inputs/solver.py",
            "infer_inputs/op_visitor.py",
        ],
        extra_compile_args=["-O3"],
    )
]

# 明确指定语言级别，确保生成正确的初始化函数
setup(
    name="infer_inputs_ext",
    ext_modules=cythonize(ext_modules, language_level="3"),  # 指定Python 3
)