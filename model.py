# -*- coding: utf-8 -*-
"""
Python module for recording Boogie models and printing them in Whiley syntax.

@author: Mark Utting
"""
import sys


class Model:
    """Stores the details of one Boogie counter-example.
    Provides facilities for simplifying the model to improve readability.
    and for printing it in Whiley-like syntax.
    """
    def __init__(self):
        """Create an empty model."""
        self.globals = {}      # the 'name -> WVal' mapping of the model
        self.records = {}      # stores the 'Select_[WField]WVal' function
        self.field_names = {}  # maps WField values to field names
        self.toInt = {}

    def concretise_dict(self, dictt):
        """Helper function for the main concretise. """
        for (name, val) in dictt.items():
            for func in (self.toInt, self.toBool, self.toRecord):
                if val in func:
                    # print("replacing", val, "by", func[val])
                    dictt[name] = func[val]

    def concretise(self):
        """Replace WVals by concrete values where possible.
        This improves readability, so should be done before printing.
        """
        self.concretise_dict(self.globals)
        for (name, rec) in self.records.items():
            self.concretise_dict(rec)

    def whiley_compound(self, val) -> str:
        """Converts records and arrays to a Whiley-like syntax."""
        if "[WField]" in val and val in self.records:
            rec = self.records[val]
            fields = list(rec.keys())
            fields.sort()
            pairs = [f + ": " + rec[f] for f in fields]
            return "{ " + ", ".join(pairs) + " }"
        elif "[Int]" in val:
            return "[ " + val + " ]"
        else:
            return val  # not a compound?

    def __str__(self):
        """Returns a human-readable version of the model.
        It will be even more readable if you call concretise first.
        Global variables are printed sorted by their names.
        """
        result = "Model:\n"
        names = list(self.globals.keys())
        names.sort()
        for name in names:
            val = self.globals[name]
            if val.startswith("|"):
                val = self.whiley_compound(val)
            result += "  {:18s} = {}\n".format(name, val)
        return result


# %% Model Reader

def ignore_pair(name, val):
    """ignores this pair of inputs."""
    pass


def store_pair(mapping, name, val):
    """Store the (name,val) pair into the given dictionary."""
    mapping[name] = val


def store_globals(model, name, val):
    """Store the global (name,val) pair into the model."""
    if name.startswith("$"):
        model.field_names[val] = name
    elif name.startswith("%lbl%"):
        pass  # ignore these
    else:
        # print("global:", name, val)
        model.globals[name] = val


def store_records(model, name, val):
    """Store a 'record field -> val' triple into model.records.
    Note that 'records' contains a nested dictionary for each record.
    """
    lhs = name.split(" ")
    if len(lhs) == 2:
        if lhs[0] not in model.records:
            model.records[lhs[0]] = {}
        rec = model.records[lhs[0]]
        rec[model.field_names[lhs[1]]] = val
    else:
        # print("ignored record select:", lhs)
        pass


def read_models(filename) -> list:
    """Reads Boogie output and parses the counter-example models.
    These are returned in the result list.
    Other lines are printed unchanged.
    """
    result = []
    curr_model = None
    curr_func = ignore_pair
    infile = open(filename, "r")
    lines = (s.strip().split(" -> ") for s in infile.readlines())
    for words in lines:
        if words == ["*** MODEL"]:
            curr_model = Model()
            curr_func = lambda n,v: store_globals(curr_model, n, v)
        elif words == ["*** END_MODEL"]:
            result.append(curr_model)
            curr_model = None
            curr_func = ignore_pair
        elif len(words) == 2 and words[1] == "{":
            # this is the start of a mapping function
            if words[0].startswith("to"):
                curr_dict = {}
                # print("==== STARTING", words[0], "====")
                setattr(curr_model, words[0], curr_dict)
                curr_func = lambda a,b: store_pair(curr_dict, a, b)
            elif words[0] == "Select_[WField]WVal":
                # print("==== STARTING select WField ====")
                curr_func = lambda n,v: store_records(curr_model, n, v)
            else:
                # print("==== ignoring ", words[0])
                curr_func = ignore_pair
        elif len(words) == 2:
            curr_func(words[0], words[1])
        elif words == ["}"]:
            curr_func = ignore_pair
        else:
            print(" -> ".join(words))   # print the original line
    return result


def main(filename):
    models = read_models(filename)
    for m in models:
        m.concretise()
        print()
        print(m)


if __name__ == "__main__":
    # execute only if run as a script
    if len(sys.argv) == 2:
        main(sys.argv[1])
    else:
        print("Usage: boogie_model.txt")
