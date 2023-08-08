""" general util functions and classes """


class UniqueNames:
    """class to provide unique names for predicates, functions, variables"""

    def __init__(self) -> None:
        self.funccounter = 0

    def function_name(self, similar: str) -> str:
        """provide a function name that is similar but unique"""
        # TODO: currently this does not guarantee uniqueness, there an anylysis of the program/rule etc... is necessary
        self.funccounter += 1
        return similar + str(self.funccounter)
