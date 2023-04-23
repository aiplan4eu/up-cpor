#!/usr/bin/env python3

from setuptools import setup # type: ignore
import up_cpor


long_description=\
'''
 ============================================================
    UP_TAMER
 ============================================================
    up_tamer is a small package that allows an exchange of
    equivalent data structures between unified_planning and Tamer.
    It automatically considers the different programming languages.
'''

setup(name='up_cpor',
      version=up_cpor.__version__,
      description='up_cpor',
      author='BGU CPOR Development Team',
      author_email='shanigu@bgu.ac.il',
      url='',
      packages=['up_cpor'],
      install_requires=['pythonnet==3.0.0'],
      python_requires='>=3.7',
      license='APACHE'
)