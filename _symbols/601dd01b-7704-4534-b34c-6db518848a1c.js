// Testimonials 1 - Updated July 6, 2025
function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
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
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
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
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
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
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
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
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
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
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
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
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
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

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
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

function createCommonjsModule(fn, basedir, module) {
	return module = {
		path: basedir,
		exports: {},
		require: function (path, base) {
			return commonjsRequire(path, (base === undefined || base === null) ? module.path : base);
		}
	}, fn(module, module.exports), module.exports;
}

function commonjsRequire () {
	throw new Error('Dynamic requires are not currently supported by @rollup/plugin-commonjs');
}

var merge_1 = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.merge = void 0;
/**
 * Merge two objects
 *
 * Replacement for Object.assign() that is not supported by IE, so it cannot be used in production yet.
 */
function merge(item1, item2, item3) {
    const result = Object.create(null);
    const items = [item1, item2, item3];
    for (let i = 0; i < 3; i++) {
        const item = items[i];
        if (typeof item === 'object' && item) {
            for (const key in item) {
                result[key] = item[key];
            }
        }
    }
    return result;
}
exports.merge = merge;

});

var customisations = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.fullCustomisations = exports.defaults = void 0;

/**
 * Default icon customisations values
 */
exports.defaults = Object.freeze({
    // Display mode
    inline: false,
    // Dimensions
    width: null,
    height: null,
    // Alignment
    hAlign: 'center',
    vAlign: 'middle',
    slice: false,
    // Transformations
    hFlip: false,
    vFlip: false,
    rotate: 0,
});
/**
 * Convert IconifyIconCustomisations to FullIconCustomisations
 */
function fullCustomisations(item) {
    return merge_1.merge(exports.defaults, item);
}
exports.fullCustomisations = fullCustomisations;

});

var shorthand = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.alignmentFromString = exports.flipFromString = void 0;
const separator = /[\s,]+/;
/**
 * Apply "flip" string to icon customisations
 */
function flipFromString(custom, flip) {
    flip.split(separator).forEach((str) => {
        const value = str.trim();
        switch (value) {
            case 'horizontal':
                custom.hFlip = true;
                break;
            case 'vertical':
                custom.vFlip = true;
                break;
        }
    });
}
exports.flipFromString = flipFromString;
/**
 * Apply "align" string to icon customisations
 */
function alignmentFromString(custom, align) {
    align.split(separator).forEach((str) => {
        const value = str.trim();
        switch (value) {
            case 'left':
            case 'center':
            case 'right':
                custom.hAlign = value;
                break;
            case 'top':
            case 'middle':
            case 'bottom':
                custom.vAlign = value;
                break;
            case 'slice':
            case 'crop':
                custom.slice = true;
                break;
            case 'meet':
                custom.slice = false;
        }
    });
}
exports.alignmentFromString = alignmentFromString;

});

var rotate = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.rotateFromString = void 0;
/**
 * Get rotation value
 */
function rotateFromString(value) {
    const units = value.replace(/^-?[0-9.]*/, '');
    function cleanup(value) {
        while (value < 0) {
            value += 4;
        }
        return value % 4;
    }
    if (units === '') {
        const num = parseInt(value);
        return isNaN(num) ? 0 : cleanup(num);
    }
    else if (units !== value) {
        let split = 0;
        switch (units) {
            case '%':
                // 25% -> 1, 50% -> 2, ...
                split = 25;
                break;
            case 'deg':
                // 90deg -> 1, 180deg -> 2, ...
                split = 90;
        }
        if (split) {
            let num = parseFloat(value.slice(0, value.length - units.length));
            if (isNaN(num)) {
                return 0;
            }
            num = num / split;
            return num % 1 === 0 ? cleanup(num) : 0;
        }
    }
    return 0;
}
exports.rotateFromString = rotateFromString;

});

var icon = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.fullIcon = exports.iconDefaults = void 0;

/**
 * Default values for IconifyIcon properties
 */
exports.iconDefaults = Object.freeze({
    body: '',
    left: 0,
    top: 0,
    width: 16,
    height: 16,
    rotate: 0,
    vFlip: false,
    hFlip: false,
});
/**
 * Create new icon with all properties
 */
function fullIcon(icon) {
    return merge_1.merge(exports.iconDefaults, icon);
}
exports.fullIcon = fullIcon;

});

var calcSize = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.calculateSize = void 0;
/**
 * Regular expressions for calculating dimensions
 */
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
/**
 * Calculate second dimension when only 1 dimension is set
 *
 * @param {string|number} size One dimension (such as width)
 * @param {number} ratio Width/height ratio.
 *      If size is width, ratio = height/width
 *      If size is height, ratio = width/height
 * @param {number} [precision] Floating number precision in result to minimize output. Default = 2
 * @return {string|number} Another dimension
 */
function calculateSize(size, ratio, precision) {
    if (ratio === 1) {
        return size;
    }
    precision = precision === void 0 ? 100 : precision;
    if (typeof size === 'number') {
        return Math.ceil(size * ratio * precision) / precision;
    }
    if (typeof size !== 'string') {
        return size;
    }
    // Split code into sets of strings and numbers
    const oldParts = size.split(unitsSplit);
    if (oldParts === null || !oldParts.length) {
        return size;
    }
    const newParts = [];
    let code = oldParts.shift();
    let isNumber = unitsTest.test(code);
    // eslint-disable-next-line no-constant-condition
    while (true) {
        if (isNumber) {
            const num = parseFloat(code);
            if (isNaN(num)) {
                newParts.push(code);
            }
            else {
                newParts.push(Math.ceil(num * ratio * precision) / precision);
            }
        }
        else {
            newParts.push(code);
        }
        // next
        code = oldParts.shift();
        if (code === void 0) {
            return newParts.join('');
        }
        isNumber = !isNumber;
    }
}
exports.calculateSize = calculateSize;

});

var builder = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.iconToSVG = void 0;

/**
 * Get preserveAspectRatio value
 */
function preserveAspectRatio(props) {
    let result = '';
    switch (props.hAlign) {
        case 'left':
            result += 'xMin';
            break;
        case 'right':
            result += 'xMax';
            break;
        default:
            result += 'xMid';
    }
    switch (props.vAlign) {
        case 'top':
            result += 'YMin';
            break;
        case 'bottom':
            result += 'YMax';
            break;
        default:
            result += 'YMid';
    }
    result += props.slice ? ' slice' : ' meet';
    return result;
}
/**
 * Get SVG attributes and content from icon + customisations
 *
 * Does not generate style to make it compatible with frameworks that use objects for style, such as React.
 * Instead, it generates verticalAlign value that should be added to style.
 *
 * Customisations should be normalised by platform specific parser.
 * Result should be converted to <svg> by platform specific parser.
 * Use replaceIDs to generate unique IDs for body.
 */
function iconToSVG(icon, customisations) {
    // viewBox
    const box = {
        left: icon.left,
        top: icon.top,
        width: icon.width,
        height: icon.height,
    };
    // Apply transformations
    const transformations = [];
    const hFlip = customisations.hFlip !== icon.hFlip;
    const vFlip = customisations.vFlip !== icon.vFlip;
    let rotation = customisations.rotate + icon.rotate;
    if (hFlip) {
        if (vFlip) {
            rotation += 2;
        }
        else {
            // Horizontal flip
            transformations.push('translate(' +
                (box.width + box.left) +
                ' ' +
                (0 - box.top) +
                ')');
            transformations.push('scale(-1 1)');
            box.top = box.left = 0;
        }
    }
    else if (vFlip) {
        // Vertical flip
        transformations.push('translate(' + (0 - box.left) + ' ' + (box.height + box.top) + ')');
        transformations.push('scale(1 -1)');
        box.top = box.left = 0;
    }
    let tempValue;
    rotation = rotation % 4;
    switch (rotation) {
        case 1:
            // 90deg
            tempValue = box.height / 2 + box.top;
            transformations.unshift('rotate(90 ' + tempValue + ' ' + tempValue + ')');
            break;
        case 2:
            // 180deg
            transformations.unshift('rotate(180 ' +
                (box.width / 2 + box.left) +
                ' ' +
                (box.height / 2 + box.top) +
                ')');
            break;
        case 3:
            // 270deg
            tempValue = box.width / 2 + box.left;
            transformations.unshift('rotate(-90 ' + tempValue + ' ' + tempValue + ')');
            break;
    }
    if (rotation % 2 === 1) {
        // Swap width/height and x/y for 90deg or 270deg rotation
        if (box.left !== 0 || box.top !== 0) {
            tempValue = box.left;
            box.left = box.top;
            box.top = tempValue;
        }
        if (box.width !== box.height) {
            tempValue = box.width;
            box.width = box.height;
            box.height = tempValue;
        }
    }
    // Calculate dimensions
    let width, height;
    if (customisations.width === null && customisations.height === null) {
        // Set height to '1em', calculate width
        height = '1em';
        width = calcSize.calculateSize(height, box.width / box.height);
    }
    else if (customisations.width !== null &&
        customisations.height !== null) {
        // Values are set
        width = customisations.width;
        height = customisations.height;
    }
    else if (customisations.height !== null) {
        // Height is set
        height = customisations.height;
        width = calcSize.calculateSize(height, box.width / box.height);
    }
    else {
        // Width is set
        width = customisations.width;
        height = calcSize.calculateSize(width, box.height / box.width);
    }
    // Check for 'auto'
    if (width === 'auto') {
        width = box.width;
    }
    if (height === 'auto') {
        height = box.height;
    }
    // Convert to string
    width = typeof width === 'string' ? width : width + '';
    height = typeof height === 'string' ? height : height + '';
    // Generate body
    let body = icon.body;
    if (transformations.length) {
        body =
            '<g transform="' + transformations.join(' ') + '">' + body + '</g>';
    }
    // Result
    const result = {
        attributes: {
            width,
            height,
            preserveAspectRatio: preserveAspectRatio(customisations),
            viewBox: box.left + ' ' + box.top + ' ' + box.width + ' ' + box.height,
        },
        body,
    };
    if (customisations.inline) {
        result.inline = true;
    }
    return result;
}
exports.iconToSVG = iconToSVG;

});

var ids = createCommonjsModule(function (module, exports) {
Object.defineProperty(exports, "__esModule", { value: true });
exports.replaceIDs = void 0;
/**
 * Regular expression for finding ids
 */
const regex = /\sid="(\S+)"/g;
/**
 * New random-ish prefix for ids
 */
const randomPrefix = 'IconifyId-' +
    Date.now().toString(16) +
    '-' +
    ((Math.random() * 0x1000000) | 0).toString(16) +
    '-';
/**
 * Counter for ids, increasing with every replacement
 */
let counter = 0;
/**
 * Replace multiple occurance of same string
 */
function strReplace(search, replace, subject) {
    let pos = 0;
    while ((pos = subject.indexOf(search, pos)) !== -1) {
        subject =
            subject.slice(0, pos) +
                replace +
                subject.slice(pos + search.length);
        pos += replace.length;
    }
    return subject;
}
/**
 * Replace IDs in SVG output with unique IDs
 * Fast replacement without parsing XML, assuming commonly used patterns and clean XML (icon should have been cleaned up with Iconify Tools or SVGO).
 */
function replaceIDs(body, prefix = randomPrefix) {
    // Find all IDs
    const ids = [];
    let match;
    while ((match = regex.exec(body))) {
        ids.push(match[1]);
    }
    if (!ids.length) {
        return body;
    }
    // Replace with unique ids
    ids.forEach(id => {
        const newID = typeof prefix === 'function' ? prefix() : prefix + counter++;
        body = strReplace('="' + id + '"', '="' + newID + '"', body);
        body = strReplace('="#' + id + '"', '="#' + newID + '"', body);
        body = strReplace('(#' + id + ')', '(#' + newID + ')', body);
    });
    return body;
}
exports.replaceIDs = replaceIDs;

});

/**
 * Default SVG attributes
 */
const svgDefaults = {
	'xmlns': 'http://www.w3.org/2000/svg',
	'xmlns:xlink': 'http://www.w3.org/1999/xlink',
	'aria-hidden': true,
	'role': 'img',
};

/**
 * Generate icon from properties
 */
function generateIcon(props) {
	let iconData = icon.fullIcon(props.icon);
	if (!iconData) {
		return {
			attributes: svgDefaults,
			body: '',
		};
	}

	const customisations$1 = merge_1.merge(customisations.defaults, props);
	const componentProps = merge_1.merge(svgDefaults);

	// Create style if missing
	let style = typeof props.style === 'string' ? props.style : '';

	// Get element properties
	for (let key in props) {
		const value = props[key];
		switch (key) {
			// Properties to ignore
			case 'icon':
			case 'style':
				break;

			// Flip as string: 'horizontal,vertical'
			case 'flip':
				shorthand.flipFromString(customisations$1, value);
				break;

			// Alignment as string
			case 'align':
				shorthand.alignmentFromString(customisations$1, value);
				break;

			// Color: copy to style
			case 'color':
				style = 'color: ' + value + '; ' + style;
				break;

			// Rotation as string
			case 'rotate':
				if (typeof value !== 'number') {
					customisations$1[key] = rotate.rotateFromString(value);
				} else {
					componentProps[key] = value;
				}
				break;

			// Remove aria-hidden
			case 'ariaHidden':
			case 'aria-hidden':
				if (value !== true && value !== 'true') {
					delete componentProps['aria-hidden'];
				}
				break;

			// Copy missing property if it does not exist in customisations
			default:
				if (customisations.defaults[key] === void 0) {
					componentProps[key] = value;
				}
		}
	}

	// Generate icon
	const item = builder.iconToSVG(iconData, customisations$1);

	// Add icon stuff
	for (let key in item.attributes) {
		componentProps[key] = item.attributes[key];
	}

	if (item.inline) {
		style = 'vertical-align: -0.125em; ' + style;
	}

	// Style
	if (style !== '') {
		componentProps.style = style;
	}

	// Counter for ids based on "id" property to render icons consistently on server and client
	let localCounter = 0;
	const id = props.id;

	// Generate HTML
	return {
		attributes: componentProps,
		body: ids.replaceIDs(
			item.body,
			id ? () => id + '-' + localCounter++ : 'iconify-svelte-'
		),
	};
}

/* generated by Svelte v3.59.1 */

function create_fragment$1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let data;

	$$self.$$set = $$new_props => {
		$$invalidate(1, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		{
			$$invalidate(0, data = generateIcon($$props));
		}
	};

	$$props = exclude_internal_props($$props);
	return [data];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
};

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.59.1 */

function create_key_block(ctx) {
	let div2;
	let span0;
	let icon;
	let t0;
	let div0;
	let raw_value = /*activeItem*/ ctx[3].quote.html + "";
	let div0_data_key_value;
	let t1;
	let div1;
	let span1;
	let t2_value = /*activeItem*/ ctx[3].name + "";
	let t2;
	let span1_data_key_value;
	let t3;
	let span2;
	let t4_value = /*activeItem*/ ctx[3].title + "";
	let t4;
	let span2_data_key_value;
	let div2_intro;
	let current;
	icon = new Component$1({ props: { icon: "fa6-solid:quote-right" } });

	return {
		c() {
			div2 = element("div");
			span0 = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			div0 = element("div");
			t1 = space();
			div1 = element("div");
			span1 = element("span");
			t2 = text(t2_value);
			t3 = space();
			span2 = element("span");
			t4 = text(t4_value);
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			span0 = claim_element(div2_nodes, "SPAN", { class: true });
			var span0_nodes = children(span0);
			claim_component(icon.$$.fragment, span0_nodes);
			span0_nodes.forEach(detach);
			t0 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true, "data-key": true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			span1 = claim_element(div1_nodes, "SPAN", { class: true, "data-key": true });
			var span1_nodes = children(span1);
			t2 = claim_text(span1_nodes, t2_value);
			span1_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			span2 = claim_element(div1_nodes, "SPAN", { class: true, "data-key": true });
			var span2_nodes = children(span2);
			t4 = claim_text(span2_nodes, t4_value);
			span2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span0, "class", "quote-icon svelte-1rjok2w");
			attr(div0, "class", "quote svelte-1rjok2w");
			attr(div0, "data-key", div0_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].quote");
			attr(span1, "class", "name svelte-1rjok2w");
			attr(span1, "data-key", span1_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].name");
			attr(span2, "class", "title svelte-1rjok2w");
			attr(span2, "data-key", span2_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].title");
			attr(div1, "class", "person svelte-1rjok2w");
			attr(div2, "class", "card svelte-1rjok2w");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, span0);
			mount_component(icon, span0, null);
			append_hydration(div2, t0);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, span1);
			append_hydration(span1, t2);
			append_hydration(div1, t3);
			append_hydration(div1, span2);
			append_hydration(span2, t4);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*activeItem*/ 8) && raw_value !== (raw_value = /*activeItem*/ ctx[3].quote.html + "")) div0.innerHTML = raw_value;
			if (!current || dirty & /*activeIndex*/ 4 && div0_data_key_value !== (div0_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].quote")) {
				attr(div0, "data-key", div0_data_key_value);
			}

			if ((!current || dirty & /*activeItem*/ 8) && t2_value !== (t2_value = /*activeItem*/ ctx[3].name + "")) set_data(t2, t2_value);

			if (!current || dirty & /*activeIndex*/ 4 && span1_data_key_value !== (span1_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].name")) {
				attr(span1, "data-key", span1_data_key_value);
			}

			if ((!current || dirty & /*activeItem*/ 8) && t4_value !== (t4_value = /*activeItem*/ ctx[3].title + "")) set_data(t4, t4_value);

			if (!current || dirty & /*activeIndex*/ 4 && span2_data_key_value !== (span2_data_key_value = "testimonials[" + /*activeIndex*/ ctx[2] + "].title")) {
				attr(span2, "data-key", span2_data_key_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			if (!div2_intro) {
				add_render_callback(() => {
					div2_intro = create_in_transition(div2, fade, {});
					div2_intro.start();
				});
			}

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			destroy_component(icon);
		}
	};
}

// (107:4) {#if testimonials.length > 1}
function create_if_block(ctx) {
	let div;
	let button0;
	let icon0;
	let button0_disabled_value;
	let t;
	let button1;
	let icon1;
	let button1_disabled_value;
	let current;
	let mounted;
	let dispose;
	icon0 = new Component$1({ props: { icon: "charm:chevron-left" } });
	icon1 = new Component$1({ props: { icon: "charm:chevron-right" } });

	return {
		c() {
			div = element("div");
			button0 = element("button");
			create_component(icon0.$$.fragment);
			t = space();
			button1 = element("button");
			create_component(icon1.$$.fragment);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			button0 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button0_nodes = children(button0);
			claim_component(icon0.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t = claim_space(div_nodes);
			button1 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button1_nodes = children(button1);
			claim_component(icon1.$$.fragment, button1_nodes);
			button1_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			button0.disabled = button0_disabled_value = /*activeIndex*/ ctx[2] === 0;
			attr(button0, "aria-label", "Show previous item");
			attr(button0, "class", "svelte-1rjok2w");
			button1.disabled = button1_disabled_value = /*activeIndex*/ ctx[2] >= /*testimonials*/ ctx[1].length - 1;
			attr(button1, "aria-label", "Show next item");
			attr(button1, "class", "svelte-1rjok2w");
			attr(div, "class", "controls svelte-1rjok2w");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, button0);
			mount_component(icon0, button0, null);
			append_hydration(div, t);
			append_hydration(div, button1);
			mount_component(icon1, button1, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*showPreviousItem*/ ctx[4]),
					listen(button1, "click", /*showNextItem*/ ctx[5])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (!current || dirty & /*activeIndex*/ 4 && button0_disabled_value !== (button0_disabled_value = /*activeIndex*/ ctx[2] === 0)) {
				button0.disabled = button0_disabled_value;
			}

			if (!current || dirty & /*activeIndex, testimonials*/ 6 && button1_disabled_value !== (button1_disabled_value = /*activeIndex*/ ctx[2] >= /*testimonials*/ ctx[1].length - 1)) {
				button1.disabled = button1_disabled_value;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div);
			destroy_component(icon0);
			destroy_component(icon1);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment(ctx) {
	let aside;
	let h2;
	let t0;
	let t1;
	let div;
	let previous_key = /*activeIndex*/ ctx[2];
	let t2;
	let current;
	let key_block = create_key_block(ctx);
	let if_block = /*testimonials*/ ctx[1].length > 1 && create_if_block(ctx);

	return {
		c() {
			aside = element("aside");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div = element("div");
			key_block.c();
			t2 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			aside = claim_element(nodes, "ASIDE", { class: true });
			var aside_nodes = children(aside);
			h2 = claim_element(aside_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(aside_nodes);
			div = claim_element(aside_nodes, "DIV", { class: true });
			var div_nodes = children(div);
			key_block.l(div_nodes);
			t2 = claim_space(div_nodes);
			if (if_block) if_block.l(div_nodes);
			div_nodes.forEach(detach);
			aside_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading svelte-1rjok2w");
			attr(div, "class", "testimonial svelte-1rjok2w");
			attr(aside, "class", "section-container svelte-1rjok2w");
		},
		m(target, anchor) {
			insert_hydration(target, aside, anchor);
			append_hydration(aside, h2);
			append_hydration(h2, t0);
			append_hydration(aside, t1);
			append_hydration(aside, div);
			key_block.m(div, null);
			append_hydration(div, t2);
			if (if_block) if_block.m(div, null);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (dirty & /*activeIndex*/ 4 && safe_not_equal(previous_key, previous_key = /*activeIndex*/ ctx[2])) {
				group_outros();
				transition_out(key_block, 1, 1, noop);
				check_outros();
				key_block = create_key_block(ctx);
				key_block.c();
				transition_in(key_block, 1);
				key_block.m(div, t2);
			} else {
				key_block.p(ctx, dirty);
			}

			if (/*testimonials*/ ctx[1].length > 1) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*testimonials*/ 2) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(key_block);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(key_block);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(aside);
			key_block.d(detaching);
			if (if_block) if_block.d();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let activeItem;
	let { props } = $$props;
	let { heading } = $$props;
	let { testimonials } = $$props;
	let activeIndex = 0;

	function showPreviousItem() {
		$$invalidate(2, activeIndex = activeIndex - 1);
	}

	function showNextItem() {
		$$invalidate(2, activeIndex = activeIndex + 1);
	}

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(6, props = $$props.props);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('testimonials' in $$props) $$invalidate(1, testimonials = $$props.testimonials);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*testimonials, activeIndex*/ 6) {
			$$invalidate(3, activeItem = testimonials[activeIndex]);
		}
	};

	return [
		heading,
		testimonials,
		activeIndex,
		activeItem,
		showPreviousItem,
		showNextItem,
		props
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 6, heading: 0, testimonials: 1 });
	}
}

export { Component as default };
