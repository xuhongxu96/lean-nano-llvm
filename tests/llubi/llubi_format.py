"""lit test format for the llubi suite (kept in a module so lit can pickle it)."""
import lit.formats


class LlubiTest(lit.formats.ShTest):
    """ShTest that marks the tests listed in `xfail.txt` as expected failures."""

    def __init__(self, xfails):
        super().__init__(execute_external=False)
        self.xfail_names = set(xfails)

    def execute(self, test, lit_config):
        if test.path_in_suite[-1] in self.xfail_names:
            test.xfails = ["*"]
        return super().execute(test, lit_config)
