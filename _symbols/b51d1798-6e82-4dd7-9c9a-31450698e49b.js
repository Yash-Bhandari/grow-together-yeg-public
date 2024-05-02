// Email your councillor - Updated May 1, 2024
function noop() { }
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function prevent_default(fn) {
    return function (event) {
        event.preventDefault();
        // @ts-ignore
        return fn.call(this, event);
    };
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}

let current_component;
function set_current_component(component) {
    current_component = component;
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}
const outroing = new Set();
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[10] = list[i][0];
	child_ctx[11] = list[i][1];
	child_ctx[12] = list[i][2];
	return child_ctx;
}

// (138:6) {#each wards as [wardName, councillor, email]}
function create_each_block(ctx) {
	let option;
	let t0_value = /*councillor*/ ctx[11] + "";
	let t0;
	let t1;
	let t2_value = /*wardName*/ ctx[10] + "";
	let t2;
	let t3;

	return {
		c() {
			option = element("option");
			t0 = text(t0_value);
			t1 = text(" (ward ");
			t2 = text(t2_value);
			t3 = text(")");
			this.h();
		},
		l(nodes) {
			option = claim_element(nodes, "OPTION", {});
			var option_nodes = children(option);
			t0 = claim_text(option_nodes, t0_value);
			t1 = claim_text(option_nodes, " (ward ");
			t2 = claim_text(option_nodes, t2_value);
			t3 = claim_text(option_nodes, ")");
			option_nodes.forEach(detach);
			this.h();
		},
		h() {
			option.__value = /*councillor*/ ctx[11];
			option.value = option.__value;
		},
		m(target, anchor) {
			insert_hydration(target, option, anchor);
			append_hydration(option, t0);
			append_hydration(option, t1);
			append_hydration(option, t2);
			append_hydration(option, t3);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(option);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let div1;
	let div0;
	let h2;
	let t0;
	let t1;
	let p;
	let t2;
	let t3;
	let form;
	let label0;
	let span;
	let t4;
	let t5;
	let input;
	let t6;
	let label1;
	let t7;
	let select;
	let t8;
	let button;
	let t9;
	let mounted;
	let dispose;
	let each_value = /*wards*/ ctx[3];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			section = element("section");
			div1 = element("div");
			div0 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			p = element("p");
			t2 = text(/*subheading*/ ctx[1]);
			t3 = space();
			form = element("form");
			label0 = element("label");
			span = element("span");
			t4 = text("Your Name:");
			t5 = space();
			input = element("input");
			t6 = space();
			label1 = element("label");
			t7 = text("Your Councillor:\n    ");
			select = element("select");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			button = element("button");
			t9 = text(/*button_text*/ ctx[2]);
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div1 = claim_element(section_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h2 = claim_element(div0_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div0_nodes);
			p = claim_element(div0_nodes, "P", { class: true });
			var p_nodes = children(p);
			t2 = claim_text(p_nodes, /*subheading*/ ctx[1]);
			p_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			form = claim_element(div1_nodes, "FORM", { class: true });
			var form_nodes = children(form);
			label0 = claim_element(form_nodes, "LABEL", { class: true });
			var label0_nodes = children(label0);
			span = claim_element(label0_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t4 = claim_text(span_nodes, "Your Name:");
			span_nodes.forEach(detach);
			t5 = claim_space(label0_nodes);

			input = claim_element(label0_nodes, "INPUT", {
				id: true,
				name: true,
				class: true,
				type: true,
				placeholder: true
			});

			label0_nodes.forEach(detach);
			t6 = claim_space(form_nodes);
			label1 = claim_element(form_nodes, "LABEL", { class: true });
			var label1_nodes = children(label1);
			t7 = claim_text(label1_nodes, "Your Councillor:\n    ");
			select = claim_element(label1_nodes, "SELECT", { id: true, name: true, class: true });
			var select_nodes = children(select);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(select_nodes);
			}

			select_nodes.forEach(detach);
			label1_nodes.forEach(detach);
			t8 = claim_space(form_nodes);
			button = claim_element(form_nodes, "BUTTON", { type: true, class: true });
			var button_nodes = children(button);
			t9 = claim_text(button_nodes, /*button_text*/ ctx[2]);
			button_nodes.forEach(detach);
			form_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(p, "class", "subheaging");
			attr(div0, "class", "heading-group svelte-13kke8f");
			attr(span, "class", "label svelte-13kke8f");
			attr(input, "id", "name");
			attr(input, "name", "name");
			attr(input, "class", "placeholder svelte-13kke8f");
			attr(input, "type", "text");
			attr(input, "placeholder", "John Doe");
			attr(label0, "class", "svelte-13kke8f");
			attr(select, "id", "councillor");
			attr(select, "name", "councillor");
			attr(select, "class", "svelte-13kke8f");
			attr(label1, "class", "label svelte-13kke8f");
			attr(button, "type", "submit");
			attr(button, "class", "button svelte-13kke8f");
			attr(form, "class", "svelte-13kke8f");
			attr(div1, "class", "box svelte-13kke8f");
			attr(section, "class", "section-container svelte-13kke8f");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			append_hydration(section, div1);
			append_hydration(div1, div0);
			append_hydration(div0, h2);
			append_hydration(h2, t0);
			append_hydration(div0, t1);
			append_hydration(div0, p);
			append_hydration(p, t2);
			append_hydration(div1, t3);
			append_hydration(div1, form);
			append_hydration(form, label0);
			append_hydration(label0, span);
			append_hydration(span, t4);
			append_hydration(label0, t5);
			append_hydration(label0, input);
			append_hydration(form, t6);
			append_hydration(form, label1);
			append_hydration(label1, t7);
			append_hydration(label1, select);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(select, null);
				}
			}

			append_hydration(form, t8);
			append_hydration(form, button);
			append_hydration(button, t9);

			if (!mounted) {
				dispose = listen(form, "submit", prevent_default(/*submit_handler*/ ctx[7]));
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subheading*/ 2) set_data(t2, /*subheading*/ ctx[1]);

			if (dirty & /*wards*/ 8) {
				each_value = /*wards*/ ctx[3];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(select, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*button_text*/ 4) set_data(t9, /*button_text*/ ctx[2]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(section);
			destroy_each(each_blocks, detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { inputs } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { button_text } = $$props;

	const wards = [
		["papastew", "Michael Janz", "michael.janz@edmonton.ca"],
		["Nakota Isga", "Andrew Knack", "andrew.knack@edmonton.ca"],
		["Anirniq", "Erin Rutherford", "erin.rutherford@edmonton.ca"],
		["Dene", "Aaron Paquette", "aaron.paquette@edmonton.ca"],
		["Ipiihkoohkanipiaohtsi", "Jennifer Rice", "jennifer.rice@edmonton.ca"],
		["Karhiio", "Keren Tang", "keren.tang@edmonton.ca"],
		["Métis", "Ashley Salvador", "ashley.salvador@edmonton.ca"],
		["O-day’min", "Anne Stevenson", "anne.stevenson@edmonton.ca"],
		["pihêsiwin", "Tim Cartmell", "tim.cartmell@edmonton.ca"],
		["sipiwiyiniwak", "Sarah Hamilton", "sarah.hamilton@edmonton.ca"],
		["Sspomitapi", "Jo-Anne Wright", "jo-anne.wright@edmonton.ca"],
		["tastawiyiniwak", "Karen Principe", "karen.principe@edmonton.ca"]
	];

	const draftLetter = (councillorName, name) => {
		const [wardName, _, councillorEmail] = wards.find(ward => ward[1] === councillorName);
		const lastName = councillorName.split(" ")[1];
		let letter = `Dear Councillor ${lastName}` + "\n\nI am writing to express my grave concern about Edmonton's rapidly rising rents and to urge you to take action. Please vote to update our zoning bylaw in order to boost our housing supply and protect affordability." + "\nRenters are not a nuisance to be regulated away. We contribute more than our fair share to Edmonton and we deserve affordable housing." + "\n\nSincerely" + `\n${name}, resident of ward ${wardName}`;
		const subjectLine = encodeURIComponent(getSubjectLine());
		letter = encodeURIComponent(letter);
		const cc = encodeURIComponent("council@edmonton.ca");
		const mailto = `mailto:${councillorEmail}?subject=${subjectLine}&body=${letter}&cc=${cc}`;
		console.log(mailto);
		window.open(mailto);
	};

	const possibleSubjectLines = [
		"Renters deserve better: Approve the new zoning bylaw",
		"Protect affordabity: Support the zoning bylaw",
		"Zoning renewal needed to maintain affordability",
		"Zoning renewal will help protect affordability"
	];

	const getSubjectLine = () => {
		let index = Math.floor(Math.random() * possibleSubjectLines.length);
		return possibleSubjectLines[index];
	};

	const submit_handler = ({ target }) => {
		const data = new FormData(target);
		console.log(data);
		draftLetter(data.get("councillor"), data.get("name"));
	};

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(5, props = $$props.props);
		if ('inputs' in $$props) $$invalidate(6, inputs = $$props.inputs);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('button_text' in $$props) $$invalidate(2, button_text = $$props.button_text);
	};

	return [
		heading,
		subheading,
		button_text,
		wards,
		draftLetter,
		props,
		inputs,
		submit_handler
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 5,
			inputs: 6,
			heading: 0,
			subheading: 1,
			button_text: 2
		});
	}
}

export { Component as default };
