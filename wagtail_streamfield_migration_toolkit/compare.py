import inspect


def get_normalised_arguments(obj):
    signature = inspect.Signature.from_callable(obj.__init__)
    _, args, kwargs = obj.deconstruct()
    return signature.bind(*args, **kwargs).arguments


def deep_deconstruct(obj):
    if isinstance(obj, list):
        return [deep_deconstruct(x) for x in obj]
    elif isinstance(obj, tuple):
        return tuple(deep_deconstruct(x) for x in obj)
    elif isinstance(obj, dict):
        return {k: deep_deconstruct(v) for k, v in obj.items()}
    elif not hasattr(obj, "deconstruct"):
        return obj

    klass, args, kwargs = obj.deconstruct()
    deconstructed_args = tuple(deep_deconstruct(x) for x in args)
    deconstructed_kwargs = {
        k: deep_deconstruct(v)
        for k, v in kwargs.items()
        if v is not inspect.Parameter.empty
    }
    signature = inspect.Signature.from_callable(obj.__init__)
    defaults = {
        k: v.default
        for k, v in signature.parameters.items()
        if k not in ("self", "kwargs")
    }
    bound = signature.bind(*deconstructed_args, **deconstructed_kwargs).arguments
    extras = bound.pop("kwargs", {})
    flat_bound = {**bound, **extras}
    return klass, {**defaults, **flat_bound}


def deconstruct_with_normalised_args(obj):
    signature = inspect.Signature.from_callable(obj.__init__)
    klass, args, kwargs = obj.deconstruct()
    return klass, signature.bind(*args, **kwargs).arguments
