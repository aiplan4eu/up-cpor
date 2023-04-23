#!/usr/bin/env python3

from setuptools import setup
from setuptools.command.install import install
import shutil
import os
import up_cpor


long_description=\
'''
 ============================================================
    UP_CPOR
 ============================================================
    up_cpor is a small package that allows an exchange of
    equivalent data structures between unified_planning and CPOR.
    It automatically considers the different programming languages.
'''


class CustomInstallCommand(install):
    def run(self):
        # Call the default run() method
        install.run(self)

        # Copy the DLL file to the installation directory
        source_path = "CPORLib/obj/Debug/netstandard2.0/CPORLib.dll".replace("/", os.path.sep)
        target_path = os.path.join(self.install_lib, "up_cpor", "CPORLib.dll")
        print(f"######self.install_lib:{self.install_lib}######")
        shutil.copy(source_path, target_path)

setup(name='up_cpor',
      version=up_cpor.__version__,
      description='up_cpor',
      author='BGU CPOR Development Team',
      author_email='shanigu@bgu.ac.il',
      url='',
      packages=['CPORLib', 'up_cpor'],
      install_requires=['pythonnet==3.0.0'],
      python_requires='>=3.7',
      # package_data={"CPORLib": ["CPORLib/obj/Debug/netstandard2.0/CPORLib.dll"]},
      cmdclass={"install": CustomInstallCommand},
      license='APACHE'
)