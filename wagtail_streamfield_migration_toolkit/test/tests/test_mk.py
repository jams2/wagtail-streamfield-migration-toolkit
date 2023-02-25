import unittest
from django.test import SimpleTestCase
from wagtail import blocks

from wagtail_streamfield_migration_toolkit.mk import (
    mk_debug,
    Cons,
    Nil,
    appendo,
    assoco,
    conda,
    conj,
    conso,
    disj,
    eq,
    fail,
    fresh,
    from_python,
    goal,
    joino,
    neq,
    notnullo,
    nullo,
    rembero,
    run_all,
    string,
    to_python,
    walk_all,
)
from wagtail_streamfield_migration_toolkit.compare import deep_deconstruct


def atomic_block_diffo(old_spec, new_spec, path, diff):
    return spec_diffo(old_spec, new_spec, path, diff)


def stream_block_diffo(old_block, new_block, path, out):
    return compound_block_diffo(old_block, new_block, path, out)


def struct_block_diffo(old_block, new_block, path, out):
    return compound_block_diffo(old_block, new_block, path, out)


def list_block_diffo(old_block, new_block, path, diff):
    def _list_block_diffo(state):
        print(to_python(walk_all(old_block, state.sub)))
        print(to_python(walk_all(new_block, state.sub)))
        breakpoint()
        return fresh(
            lambda _, __, old_spec, new_spec: conj(
                eq((_, old_spec), old_block),
                eq((__, new_spec), new_block),
                fresh(
                    lambda _, __, old_child, new_child, next_path: conj(
                        assoco(string("child_block"), old_spec, old_child),
                        assoco(string("child_block"), new_spec, new_child),
                        joino(path, string("item"), string("."), next_path),
                        same_blocko(old_child, new_child, next_path, diff),
                    )
                ),
            )
        )(state)

    return goal(_list_block_diffo)


def spec_diffo(old_spec, new_spec, path, diff):
    return disj(
        nullo(old_spec) & nullo(new_spec) & nullo(diff),
        fresh(
            lambda k, d, e, rest_old_spec, rest_new_spec: conj(
                notnullo(old_spec),
                notnullo(new_spec),
                conso((k, d), rest_old_spec, old_spec),
                conso((k, e), rest_new_spec, new_spec),
                neq(k, string("local_blocks")),
                neq(k, string("child_block")),
                disj(
                    eq(d, e) & spec_diffo(rest_old_spec, rest_new_spec, path, diff),
                    fresh(
                        lambda res: conj(
                            neq(d, e),
                            conso((path, string("change_opt"), k, d, e), res, diff),
                            spec_diffo(rest_old_spec, rest_new_spec, path, res),
                        )
                    ),
                ),
            ),
        ),
    )


def compound_block_diffo(old_block, new_block, path, diff):
    return fresh(
        lambda _, __, old_spec, new_spec: conj(
            eq((_, old_spec), old_block),
            eq((__, new_spec), new_block),
            fresh(
                lambda _, __, old_children, new_children, this_diff: conj(
                    assoco(string("local_blocks"), old_spec, (_, old_children)),
                    assoco(string("local_blocks"), new_spec, (__, new_children)),
                    map_child_blocks(old_children, new_children, path, diff),
                )
            ),
        )
    )


def map_child_blocks(old_blocks, new_blocks, path, diff):
    def _map_child_blocks(
        name, spec, rest_old_blocks, rest_new_blocks, this_path, next_diff, child_diff
    ):
        return disj(
            # old blocks null, new blocks null - done
            nullo(old_blocks) & nullo(new_blocks) & nullo(diff),
            conj(
                # old blocks not null, new blocks null - old block removed
                notnullo(old_blocks) & nullo(new_blocks),
                conso((name, spec), rest_old_blocks, old_blocks),
                conso((path, string("remove"), name), next_diff, diff),
                map_child_blocks(rest_old_blocks, new_blocks, path, next_diff),
            ),
            conj(
                # old blocks null, new blocks not null - new block added
                nullo(old_blocks) & notnullo(new_blocks),
                conso((name, spec), rest_new_blocks, new_blocks),
                conso((path, string("add"), name), next_diff, diff),
                map_child_blocks(old_blocks, rest_new_blocks, path, next_diff),
            ),
            conj(
                # old blocks not null, new blocks not null - map old block to new block
                notnullo(old_blocks) & notnullo(new_blocks),
                conso((name, spec), rest_old_blocks, old_blocks),
                joino(path, name, string("."), this_path),
                map_child_block(
                    name, spec, new_blocks, this_path, rest_new_blocks, child_diff
                ),
                appendo(child_diff, next_diff, diff),
                map_child_blocks(rest_old_blocks, rest_new_blocks, path, next_diff),
            ),
            conj(
                # couldn't map it yet, send it to the end with a flag, maybe it was removed
                notnullo(old_blocks) & notnullo(new_blocks),
                fresh(
                    lambda tmp: conj(
                        conso((name, spec), tmp, old_blocks),
                        appendo(
                            tmp, Cons(("unmapped", name, spec), Nil()), rest_old_blocks
                        ),
                        map_child_blocks(rest_old_blocks, new_blocks, path, diff),
                    )
                ),
            ),
            conj(
                # All old blocks are unmapped
                notnullo(old_blocks),
                fresh(
                    lambda diff1, diff2: conj(
                        mark_unmapped_removo(old_blocks, path, diff1),
                        mark_all_addo(new_blocks, path, diff2),
                        appendo(diff1, diff2, diff),
                    )
                ),
            ),
        )

    return fresh(_map_child_blocks)


def mark_unmapped_removo(blocks, path, diff):
    return disj(
        nullo(blocks) & nullo(diff),
        fresh(
            lambda name, _, rest, this_path, next_diff: conj(
                conso(("unmapped", name, _), rest, blocks),
                conso((path, "remove", name), next_diff, diff),
                mark_unmapped_removo(rest, path, next_diff),
            )
        ),
    )


def mark_all_addo(blocks, path, diff):
    return disj(
        nullo(blocks) & nullo(diff),
        fresh(
            lambda name, _, rest, next_diff: conj(
                conso((name, _), rest, blocks),
                conso((path, "add", name), next_diff, diff),
                mark_all_addo(rest, path, next_diff),
            )
        ),
    )


def map_child_block(name, spec, new_blocks, path, rest_new_blocks, diff):
    def _map_child_block(state):
        return fresh(
            lambda new_name, new_spec, next_diff, next_path: conj(
                conso((new_name, new_spec), rest_new_blocks, new_blocks),
                same_blocko(spec, new_spec, path, next_diff),
                conda(
                    eq(name, new_name) & eq(next_diff, diff),
                    conj(
                        neq(name, new_name),
                        conso((path, "rename", new_name), next_diff, diff),
                    ),
                ),
            )
        )(state)

    return goal(_map_child_block)


def same_blocko(old_block_spec, new_block_spec, path, diff):
    # Block specs here are (type, args) tuples from deep deconstruct
    def _same_blocko(state):
        return fresh(
            lambda old_type, new_type, old_spec, new_spec: conj(
                eq((old_type, old_spec), old_block_spec),
                eq((new_type, new_spec), new_block_spec),
                eq(old_type, new_type),
                disj(
                    atomic_block_diffo(old_spec, new_spec, path, diff),
                    stream_block_diffo(old_block_spec, new_block_spec, path, diff),
                    mk_debug(list_block_diffo(old_block_spec, new_block_spec, path, diff)),
                ),
            )
        )(state)

    return goal(_same_blocko)


@unittest.skip
class TestMkCompare(SimpleTestCase):
    def test_stream_child_spec_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("text", blocks.CharBlock(max_length=11))])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "change_opt", "max_length", None, 11)]])

    def test_stream_child_removed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "remove")]])

    def test_stream_child_added(self):
        block_1 = blocks.StreamBlock([])
        block_2 = blocks.StreamBlock([("text", blocks.CharBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$", "add", "text")]])

    def test_stream_child_name_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("not_text", blocks.CharBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "rename", "not_text")]])

    def test_stream_child_removed_when_multiple_child_blocks(self):
        block_1 = blocks.StreamBlock(
            [("text", blocks.CharBlock()), ("number", blocks.IntegerBlock())]
        )
        block_2 = blocks.StreamBlock([("number", blocks.IntegerBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "remove")]])

    def test_nested_stream_child_name_changed(self):
        inner_stream_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        inner_stream_2 = blocks.StreamBlock([("not_text", blocks.CharBlock())])
        block_1 = blocks.StreamBlock([("inner_stream", inner_stream_1)])
        block_2 = blocks.StreamBlock([("inner_stream", inner_stream_2)])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.inner_stream.text", "rename", "not_text")]])

    def test_different_block_types_fails(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock([("not_text", blocks.IntegerBlock())])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "remove"), ("$", "add", "not_text")]])

    def test_struct_block(self):
        struct_1 = blocks.StructBlock([("number", blocks.IntegerBlock())])
        struct_2 = blocks.StructBlock(
            [("more_number", blocks.IntegerBlock(min_value=11))]
        )
        block_1 = blocks.StreamBlock([("struct", struct_1)])
        block_2 = blocks.StreamBlock([("struct", struct_2)])
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(
            result,
            [
                [
                    ("$.struct.number", "rename", "more_number"),
                    ("$.struct.number", "change_opt", "min_value", None, 11),
                ]
            ],
        )

    def test_stream_child_name_and_spec_changed(self):
        block_1 = blocks.StreamBlock([("text", blocks.CharBlock())])
        block_2 = blocks.StreamBlock(
            [
                ("not_text", blocks.CharBlock(required=False, max_length=1)),
                ("really_not_text", blocks.CharBlock(min_length=12)),
            ]
        )
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: stream_block_diffo(a, b, string("$"), q))
        self.assertEqual(
            result,
            [
                [
                    [
                        ("$.text", "rename", "not_text"),
                        ("$.text", "change_opt", "required", True, False),
                        ("$.text", "change_opt", "max_length", None, 1),
                    ],
                    [
                        ("$.text", "rename", "really_not_text"),
                        ("$.text", "change_opt", "min_length", None, 12),
                    ],
                ]
            ],
        )


class TestListBlock(SimpleTestCase):
    def test_list_block_atomic_child(self):
        block_1 = blocks.StreamBlock([("list", blocks.ListBlock(blocks.CharBlock()))])
        block_2 = blocks.StreamBlock(
            [("list", blocks.ListBlock(blocks.CharBlock(min_length=42)))]
        )
        a = from_python(deep_deconstruct(block_1))
        b = from_python(deep_deconstruct(block_2))
        result = run_all(lambda q: same_blocko(a, b, string("$"), q))
        self.assertEqual(result, [[("$.text", "remove"), ("$", "add", "not_text")]])


@unittest.skip
class TestMkBackwards(SimpleTestCase):
    def test_second_block_from_diff(self):
        block_1 = blocks.CharBlock(required=True)
        _, args = deep_deconstruct(block_1)
        changes = from_python([(string("$"), "change_opt", "required", True, False)])
        result = run_all(
            lambda q: spec_diffo(from_python(args), q, string("$"), changes)
        )
        self.assertEqual(
            result,
            [
                [
                    ("required", False),
                    ("help_text", None),
                    ("max_length", None),
                    ("min_length", None),
                    ("validators", ()),
                ]
            ],
        )

    def test_first_block_from_diff(self):
        block_1 = blocks.CharBlock(required=True)
        _, args = deep_deconstruct(block_1)
        changes = from_python(
            [
                ("$", "change_opt", "required", False, True),
                ("$", "change_opt", "help_text", "foobar", None),
            ]
        )
        result = run_all(
            lambda q: spec_diffo(q, from_python(args), string("$"), changes)
        )
        self.assertEqual(
            result,
            [
                [
                    ("required", False),
                    ("help_text", "foobar"),
                    ("max_length", None),
                    ("min_length", None),
                    ("validators", ()),
                ]
            ],
        )
