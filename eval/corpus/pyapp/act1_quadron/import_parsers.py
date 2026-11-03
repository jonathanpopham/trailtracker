try:
    from integrations import INTEGRATION_PARSERS as _INT_PARSERS
except ImportError:
    _INT_PARSERS = {}


def load_parsers():
    return _INT_PARSERS
