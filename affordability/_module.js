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
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
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
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
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
function empty() {
    return text('');
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
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
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
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
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
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
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
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
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

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link0;
	let link0_href_value;
	let link1;
	let script0;
	let script0_src_value;
	let script1;
	let t0;
	let title_value;
	let meta2;
	let meta3;
	let meta4;
	let meta4_content_value;
	let style;
	let t1;
	document.title = title_value = /*title*/ ctx[1];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link0 = element("link");
			link1 = element("link");
			script0 = element("script");
			script1 = element("script");
			t0 = text("(function(w,d,e,u,f,l,n){w[f]=w[f]||function(){(w[f].q=w[f].q||[])\n    .push(arguments);},l=d.createElement(e),l.async=1,l.src=u,\n    n=d.getElementsByTagName(e)[0],n.parentNode.insertBefore(l,n);})\n    (window,document,'script','https://assets.mailerlite.com/js/universal.js','ml');\n    ml('account', '511328');\n");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			style = element("style");
			t1 = text("/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #027648;\n  --color1: #4C5760;\n  \n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  max-height: 80px;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n\n.content a {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    transition: var(--transition, 0.1s border);\n}");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1l738vf', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });

			link0 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			script0 = claim_element(head_nodes, "SCRIPT", { src: true, "data-website-id": true });
			var script0_nodes = children(script0);
			script0_nodes.forEach(detach);
			script1 = claim_element(head_nodes, "SCRIPT", {});
			var script1_nodes = children(script1);
			t0 = claim_text(script1_nodes, "(function(w,d,e,u,f,l,n){w[f]=w[f]||function(){(w[f].q=w[f].q||[])\n    .push(arguments);},l=d.createElement(e),l.async=1,l.src=u,\n    n=d.getElementsByTagName(e)[0],n.parentNode.insertBefore(l,n);})\n    (window,document,'script','https://assets.mailerlite.com/js/universal.js','ml');\n    ml('account', '511328');\n");
			script1_nodes.forEach(detach);
			meta2 = claim_element(head_nodes, "META", { property: true, content: true });
			meta3 = claim_element(head_nodes, "META", { property: true, content: true });
			meta4 = claim_element(head_nodes, "META", { property: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t1 = claim_text(style_nodes, "/* Reset & standardize default styles */\n@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options */\n  --color-accent: #027648;\n  --color1: #4C5760;\n  \n  /* Base values */\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n}\n\n/* Root element (use instead of `body`) */\n#page {\n  font-family: system-ui, sans-serif;\n  color: #111;\n  line-height: 1.5;\n  font-size: 1.125rem;\n  background: white;\n}\n\n/* Elements */\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  padding: 5rem 2rem;\n}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0; /* reset */\n  max-height: 80px;\n}\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n\n.content a {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    transition: var(--transition, 0.1s border);\n}");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link0, "rel", "icon");
			attr(link0, "type", "image/png");
			attr(link0, "sizes", "32x32");
			attr(link0, "href", link0_href_value = /*favicon*/ ctx[0].url);
			attr(link1, "rel", "preconnect");
			attr(link1, "href", "https://fonts.bunny.net");
			script0.async = true;
			if (!src_url_equal(script0.src, script0_src_value = "https://analytics.umami.is/script.js")) attr(script0, "src", script0_src_value);
			attr(script0, "data-website-id", "541fddec-8517-45e6-b5e5-6a9e36cb83c3");
			attr(meta2, "property", "og:title");
			attr(meta2, "content", /*title*/ ctx[1]);
			attr(meta3, "property", "og:type");
			attr(meta3, "content", "article");
			attr(meta4, "property", "og:image");
			attr(meta4, "content", meta4_content_value = /*preview_image*/ ctx[2].url);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, script0);
			append_hydration(document.head, script1);
			append_hydration(script1, t0);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, style);
			append_hydration(style, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link0_href_value !== (link0_href_value = /*favicon*/ ctx[0].url)) {
				attr(link0, "href", link0_href_value);
			}

			if (dirty & /*title*/ 2 && title_value !== (title_value = /*title*/ ctx[1])) {
				document.title = title_value;
			}

			if (dirty & /*title*/ 2) {
				attr(meta2, "content", /*title*/ ctx[1]);
			}

			if (dirty & /*preview_image*/ 4 && meta4_content_value !== (meta4_content_value = /*preview_image*/ ctx[2].url)) {
				attr(meta4, "content", meta4_content_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link0);
			detach(link1);
			detach(script0);
			detach(script1);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(3, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(4, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(2, preview_image = $$props.preview_image);
	};

	return [favicon, title, preview_image, color1, color2];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			color1: 3,
			color2: 4,
			favicon: 0,
			title: 1,
			preview_image: 2
		});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
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
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
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
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
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
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].link;
	return child_ctx;
}

// (115:6) {#if logo.image.url}
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", {
				src: true,
				alt: true,
				style: true,
				class: true
			});

			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			attr(img, "class", "svelte-nnp8i3");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*logo_width*/ 4) {
				set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (121:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[12].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-nnp8i3");
			attr(a, "href", a_href_value = /*link*/ ctx[12].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (128:6) {#if logo.image.url}
function create_if_block_1$1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", {
				class: true,
				src: true,
				alt: true,
				style: true
			});

			this.h();
		},
		h() {
			attr(img, "class", "logo svelte-nnp8i3");
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
			set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*logo_width*/ 4) {
				set_style(img, "max-width", /*logo_width*/ ctx[2] + "px");
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (139:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-nnp8i3");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-nnp8i3");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[10]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (141:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[12].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[12].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let t1_value = /*logo*/ ctx[0].title + "";
	let t1;
	let t2;
	let nav;
	let t3;
	let div1;
	let a1;
	let t4;
	let t5_value = /*logo*/ ctx[0].title + "";
	let t5;
	let t6;
	let button;
	let icon;
	let t7;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*logo*/ ctx[0].image.url && create_if_block_2(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let if_block1 = /*logo*/ ctx[0].image.url && create_if_block_1$1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[3] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			t1 = text(t1_value);
			t2 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t4 = space();
			t5 = text(t5_value);
			t6 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t7 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			t0 = claim_space(a0_nodes);
			t1 = claim_text(a0_nodes, t1_value);
			a0_nodes.forEach(detach);
			t2 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			t4 = claim_space(a1_nodes);
			t5 = claim_text(a1_nodes, t5_value);
			a1_nodes.forEach(detach);
			t6 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t7 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-nnp8i3");
			attr(nav, "class", "svelte-nnp8i3");
			attr(div0, "class", "desktop-nav svelte-nnp8i3");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-nnp8i3");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-nnp8i3");
			attr(header, "class", "section-container svelte-nnp8i3");
			attr(div2, "class", "section");
			attr(div2, "id", "section-17ec1161");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(a0, t0);
			append_hydration(a0, t1);
			append_hydration(div0, t2);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t3);
			append_hydration(header, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(a1, t4);
			append_hydration(a1, t5);
			append_hydration(div1, t6);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t7);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[9]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (/*logo*/ ctx[0].image.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2(ctx);
					if_block0.c();
					if_block0.m(a0, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if ((!current || dirty & /*logo*/ 1) && t1_value !== (t1_value = /*logo*/ ctx[0].title + "")) set_data(t1, t1_value);

			if (dirty & /*site_nav*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (/*logo*/ ctx[0].image.url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1$1(ctx);
					if_block1.c();
					if_block1.m(a1, t4);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if ((!current || dirty & /*logo*/ 1) && t5_value !== (t5_value = /*logo*/ ctx[0].title + "")) set_data(t5, t5_value);

			if (/*mobileNavOpen*/ ctx[3]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 8) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			destroy_each(each_blocks, detaching);
			if (if_block1) if_block1.d();
			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let { logo_width } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(3, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(3, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(4, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(5, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(6, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(7, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(8, preview_image = $$props.preview_image);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
		if ('logo_width' in $$props) $$invalidate(2, logo_width = $$props.logo_width);
	};

	return [
		logo,
		site_nav,
		logo_width,
		mobileNavOpen,
		color1,
		color2,
		favicon,
		title,
		preview_image,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			color1: 4,
			color2: 5,
			favicon: 6,
			title: 7,
			preview_image: 8,
			logo: 0,
			site_nav: 1,
			logo_width: 2
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_if_block_1$2(ctx) {
	let div;
	let t0;
	let t1;

	return {
		c() {
			div = element("div");
			t0 = text("By ");
			t1 = text(/*author*/ ctx[3]);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t0 = claim_text(div_nodes, "By ");
			t1 = claim_text(div_nodes, /*author*/ ctx[3]);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "author svelte-7kabnb");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t0);
			append_hydration(div, t1);
		},
		p(ctx, dirty) {
			if (dirty & /*author*/ 8) set_data(t1, /*author*/ ctx[3]);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (46:2) {#if image.url}
function create_if_block$2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[2].alt);
			attr(img, "class", "svelte-7kabnb");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*image*/ 4 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[2].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 4 && img_alt_value !== (img_alt_value = /*image*/ ctx[2].alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment$3(ctx) {
	let div;
	let header;
	let h1;
	let t0;
	let t1;
	let span;
	let t2;
	let t3;
	let t4;
	let t5;
	let hr;
	let if_block0 = /*author*/ ctx[3] && create_if_block_1$2(ctx);
	let if_block1 = /*image*/ ctx[2].url && create_if_block$2(ctx);

	return {
		c() {
			div = element("div");
			header = element("header");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			span = element("span");
			t2 = text(/*subhead*/ ctx[1]);
			t3 = space();
			if (if_block0) if_block0.c();
			t4 = space();
			if (if_block1) if_block1.c();
			t5 = space();
			hr = element("hr");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			header = claim_element(div_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			h1 = claim_element(header_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			span = claim_element(header_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t2 = claim_text(span_nodes, /*subhead*/ ctx[1]);
			span_nodes.forEach(detach);
			t3 = claim_space(header_nodes);
			if (if_block0) if_block0.l(header_nodes);
			t4 = claim_space(header_nodes);
			if (if_block1) if_block1.l(header_nodes);
			t5 = claim_space(header_nodes);
			hr = claim_element(header_nodes, "HR", { class: true });
			header_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "heading svelte-7kabnb");
			attr(span, "class", "subhead svelte-7kabnb");
			attr(hr, "class", "svelte-7kabnb");
			attr(header, "class", "section-container svelte-7kabnb");
			attr(div, "class", "section");
			attr(div, "id", "section-11e0e6ac");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, header);
			append_hydration(header, h1);
			append_hydration(h1, t0);
			append_hydration(header, t1);
			append_hydration(header, span);
			append_hydration(span, t2);
			append_hydration(header, t3);
			if (if_block0) if_block0.m(header, null);
			append_hydration(header, t4);
			if (if_block1) if_block1.m(header, null);
			append_hydration(header, t5);
			append_hydration(header, hr);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*subhead*/ 2) set_data(t2, /*subhead*/ ctx[1]);

			if (/*author*/ ctx[3]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_1$2(ctx);
					if_block0.c();
					if_block0.m(header, t4);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (/*image*/ ctx[2].url) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block$2(ctx);
					if_block1.c();
					if_block1.m(header, t5);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { heading } = $$props;
	let { subhead } = $$props;
	let { image } = $$props;
	let { author } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(4, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(5, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(6, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(7, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(8, preview_image = $$props.preview_image);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subhead' in $$props) $$invalidate(1, subhead = $$props.subhead);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
		if ('author' in $$props) $$invalidate(3, author = $$props.author);
	};

	return [heading, subhead, image, author, color1, color2, favicon, title, preview_image];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			color1: 4,
			color2: 5,
			favicon: 6,
			title: 7,
			preview_image: 8,
			heading: 0,
			subhead: 1,
			image: 2,
			author: 3
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i];
	return child_ctx;
}

// (80:2) {#each data as city}
function create_each_block$1(ctx) {
	let tr;
	let td0;
	let t0_value = /*city*/ ctx[9].city + "";
	let t0;
	let t1;
	let td1;
	let t2_value = /*moneyFormatter*/ ctx[2].format(/*city*/ ctx[9].rent) + "";
	let t2;
	let t3;
	let td2;
	let t4;
	let t5_value = /*city*/ ctx[9].change + "";
	let t5;
	let t6;
	let t7;

	return {
		c() {
			tr = element("tr");
			td0 = element("td");
			t0 = text(t0_value);
			t1 = space();
			td1 = element("td");
			t2 = text(t2_value);
			t3 = space();
			td2 = element("td");
			t4 = text("+");
			t5 = text(t5_value);
			t6 = text("%");
			t7 = space();
			this.h();
		},
		l(nodes) {
			tr = claim_element(nodes, "TR", { class: true });
			var tr_nodes = children(tr);
			td0 = claim_element(tr_nodes, "TD", { class: true });
			var td0_nodes = children(td0);
			t0 = claim_text(td0_nodes, t0_value);
			td0_nodes.forEach(detach);
			t1 = claim_space(tr_nodes);
			td1 = claim_element(tr_nodes, "TD", { class: true });
			var td1_nodes = children(td1);
			t2 = claim_text(td1_nodes, t2_value);
			td1_nodes.forEach(detach);
			t3 = claim_space(tr_nodes);
			td2 = claim_element(tr_nodes, "TD", { class: true });
			var td2_nodes = children(td2);
			t4 = claim_text(td2_nodes, "+");
			t5 = claim_text(td2_nodes, t5_value);
			t6 = claim_text(td2_nodes, "%");
			td2_nodes.forEach(detach);
			t7 = claim_space(tr_nodes);
			tr_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(td0, "class", "svelte-yi0kic");
			attr(td1, "class", "numericCell svelte-yi0kic");
			attr(td2, "class", "numericCell svelte-yi0kic");
			attr(tr, "class", "svelte-yi0kic");
		},
		m(target, anchor) {
			insert_hydration(target, tr, anchor);
			append_hydration(tr, td0);
			append_hydration(td0, t0);
			append_hydration(tr, t1);
			append_hydration(tr, td1);
			append_hydration(td1, t2);
			append_hydration(tr, t3);
			append_hydration(tr, td2);
			append_hydration(td2, t4);
			append_hydration(td2, t5);
			append_hydration(td2, t6);
			append_hydration(tr, t7);
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && t0_value !== (t0_value = /*city*/ ctx[9].city + "")) set_data(t0, t0_value);
			if (dirty & /*data*/ 1 && t2_value !== (t2_value = /*moneyFormatter*/ ctx[2].format(/*city*/ ctx[9].rent) + "")) set_data(t2, t2_value);
			if (dirty & /*data*/ 1 && t5_value !== (t5_value = /*city*/ ctx[9].change + "")) set_data(t5, t5_value);
		},
		d(detaching) {
			if (detaching) detach(tr);
		}
	};
}

function create_fragment$4(ctx) {
	let div1;
	let div0;
	let table;
	let tr0;
	let th0;
	let t0;
	let t1;
	let th1;
	let t2;
	let t3;
	let th2;
	let t4;
	let t5;
	let tbody;
	let t6;
	let tfoot;
	let tr1;
	let td;
	let t7;
	let a;
	let t8_value = /*data_source*/ ctx[1].name + "";
	let t8;
	let a_href_value;
	let each_value = /*data*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			table = element("table");
			tr0 = element("tr");
			th0 = element("th");
			t0 = text("City");
			t1 = space();
			th1 = element("th");
			t2 = text("Rent (1 Bed)");
			t3 = space();
			th2 = element("th");
			t4 = text("Change since last year");
			t5 = space();
			tbody = element("tbody");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t6 = space();
			tfoot = element("tfoot");
			tr1 = element("tr");
			td = element("td");
			t7 = text("Data source: ");
			a = element("a");
			t8 = text(t8_value);
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			table = claim_element(div0_nodes, "TABLE", { class: true });
			var table_nodes = children(table);
			tr0 = claim_element(table_nodes, "TR", { class: true });
			var tr0_nodes = children(tr0);
			th0 = claim_element(tr0_nodes, "TH", { class: true });
			var th0_nodes = children(th0);
			t0 = claim_text(th0_nodes, "City");
			th0_nodes.forEach(detach);
			t1 = claim_space(tr0_nodes);
			th1 = claim_element(tr0_nodes, "TH", { class: true });
			var th1_nodes = children(th1);
			t2 = claim_text(th1_nodes, "Rent (1 Bed)");
			th1_nodes.forEach(detach);
			t3 = claim_space(tr0_nodes);
			th2 = claim_element(tr0_nodes, "TH", { class: true });
			var th2_nodes = children(th2);
			t4 = claim_text(th2_nodes, "Change since last year");
			th2_nodes.forEach(detach);
			tr0_nodes.forEach(detach);
			t5 = claim_space(table_nodes);
			tbody = claim_element(table_nodes, "TBODY", { class: true });
			var tbody_nodes = children(tbody);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(tbody_nodes);
			}

			tbody_nodes.forEach(detach);
			t6 = claim_space(table_nodes);
			tfoot = claim_element(table_nodes, "TFOOT", {});
			var tfoot_nodes = children(tfoot);
			tr1 = claim_element(tfoot_nodes, "TR", { class: true });
			var tr1_nodes = children(tr1);
			td = claim_element(tr1_nodes, "TD", { colspan: true, class: true });
			var td_nodes = children(td);
			t7 = claim_text(td_nodes, "Data source: ");
			a = claim_element(td_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t8 = claim_text(a_nodes, t8_value);
			a_nodes.forEach(detach);
			td_nodes.forEach(detach);
			tr1_nodes.forEach(detach);
			tfoot_nodes.forEach(detach);
			table_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(th0, "class", "svelte-yi0kic");
			attr(th1, "class", "svelte-yi0kic");
			attr(th2, "class", "svelte-yi0kic");
			attr(tr0, "class", "svelte-yi0kic");
			attr(tbody, "class", "svelte-yi0kic");
			attr(a, "href", a_href_value = /*data_source*/ ctx[1].url);
			attr(a, "class", "svelte-yi0kic");
			attr(td, "colspan", "3");
			attr(td, "class", "svelte-yi0kic");
			attr(tr1, "class", "svelte-yi0kic");
			attr(table, "class", "svelte-yi0kic");
			attr(div0, "class", "container svelte-yi0kic");
			attr(div1, "class", "section");
			attr(div1, "id", "section-d24abdc6");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, table);
			append_hydration(table, tr0);
			append_hydration(tr0, th0);
			append_hydration(th0, t0);
			append_hydration(tr0, t1);
			append_hydration(tr0, th1);
			append_hydration(th1, t2);
			append_hydration(tr0, t3);
			append_hydration(tr0, th2);
			append_hydration(th2, t4);
			append_hydration(table, t5);
			append_hydration(table, tbody);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(tbody, null);
				}
			}

			append_hydration(table, t6);
			append_hydration(table, tfoot);
			append_hydration(tfoot, tr1);
			append_hydration(tr1, td);
			append_hydration(td, t7);
			append_hydration(td, a);
			append_hydration(a, t8);
		},
		p(ctx, [dirty]) {
			if (dirty & /*data, moneyFormatter*/ 5) {
				each_value = /*data*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(tbody, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*data_source*/ 2 && t8_value !== (t8_value = /*data_source*/ ctx[1].name + "")) set_data(t8, t8_value);

			if (dirty & /*data_source*/ 2 && a_href_value !== (a_href_value = /*data_source*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;
	let { data } = $$props;
	let { data_source } = $$props;

	const moneyFormatter = new Intl.NumberFormat('en-US',
	{
			style: 'currency',
			currency: 'USD',
			maximumFractionDigits: 0
		});

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(3, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(4, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(6, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(7, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(8, content = $$props.content);
		if ('data' in $$props) $$invalidate(0, data = $$props.data);
		if ('data_source' in $$props) $$invalidate(1, data_source = $$props.data_source);
	};

	return [
		data,
		data_source,
		moneyFormatter,
		color1,
		color2,
		favicon,
		title,
		preview_image,
		content
	];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			color1: 3,
			color2: 4,
			favicon: 5,
			title: 6,
			preview_image: 7,
			content: 8,
			data: 0,
			data_source: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-1c8b26e1");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$6(ctx) {
	let div;
	let section;
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			div = element("div");
			section = element("section");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);
			section = claim_element(div_nodes, "SECTION", { class: true });
			var section_nodes = children(section);

			img = claim_element(section_nodes, "IMG", {
				src: true,
				alt: true,
				style: true,
				class: true
			});

			section_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*image*/ ctx[0].alt);
			set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			attr(img, "class", "svelte-1qe5oiy");
			attr(section, "class", "section-container svelte-1qe5oiy");
			attr(div, "class", "section");
			attr(div, "id", "section-72ab4c30");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, section);
			append_hydration(section, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*image*/ 1 && !src_url_equal(img.src, img_src_value = /*image*/ ctx[0].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*image*/ 1 && img_alt_value !== (img_alt_value = /*image*/ ctx[0].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (dirty & /*max_height*/ 2) {
				set_style(img, "max-height", /*max_height*/ ctx[1] + "px");
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { image } = $$props;
	let { max_height } = $$props;
	let { caption } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(2, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(3, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(4, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(5, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(6, preview_image = $$props.preview_image);
		if ('image' in $$props) $$invalidate(0, image = $$props.image);
		if ('max_height' in $$props) $$invalidate(1, max_height = $$props.max_height);
		if ('caption' in $$props) $$invalidate(7, caption = $$props.caption);
	};

	return [image, max_height, color1, color2, favicon, title, preview_image, caption];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			color1: 2,
			color2: 3,
			favicon: 4,
			title: 5,
			preview_image: 6,
			image: 0,
			max_height: 1,
			caption: 7
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$7(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-19f40b4b");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$8(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-8be6d490");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$9(ctx) {
	let div2;
	let div1;
	let div0;
	let raw_value = /*content*/ ctx[0].html + "";

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container content svelte-1b9cr7a");
			attr(div1, "class", "section");
			attr(div2, "class", "section");
			attr(div2, "id", "section-1019baf1");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = raw_value;
		},
		p(ctx, [dirty]) {
			if (dirty & /*content*/ 1 && raw_value !== (raw_value = /*content*/ ctx[0].html + "")) div0.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { content } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(1, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(2, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(5, preview_image = $$props.preview_image);
		if ('content' in $$props) $$invalidate(0, content = $$props.content);
	};

	return [content, color1, color2, favicon, title, preview_image];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			color1: 1,
			color2: 2,
			favicon: 3,
			title: 4,
			preview_image: 5,
			content: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	child_ctx[10] = list[i].icon;
	return child_ctx;
}

// (86:6) {#each social as { link, icon }}
function create_each_block$2(ctx) {
	let a;
	let span;
	let icon;
	let t0;
	let t1_value = /*link*/ ctx[9].label + "";
	let t1;
	let t2;
	let a_href_value;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[10] } });

	return {
		c() {
			a = element("a");
			span = element("span");
			create_component(icon.$$.fragment);
			t0 = space();
			t1 = text(t1_value);
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			claim_component(icon.$$.fragment, span_nodes);
			span_nodes.forEach(detach);
			t0 = claim_space(a_nodes);
			t1 = claim_text(a_nodes, t1_value);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "icon svelte-1mgn2yk");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			attr(a, "class", "svelte-1mgn2yk");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			mount_component(icon, span, null);
			append_hydration(a, t0);
			append_hydration(a, t1);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 4) icon_changes.icon = /*icon*/ ctx[10];
			icon.$set(icon_changes);
			if ((!current || dirty & /*social*/ 4) && t1_value !== (t1_value = /*link*/ ctx[9].label + "")) set_data(t1, t1_value);

			if (!current || dirty & /*social*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

function create_fragment$a(ctx) {
	let div15;
	let section;
	let div2;
	let h2;
	let t0;
	let t1;
	let div0;
	let raw_value = /*subheading*/ ctx[1].html + "";
	let t2;
	let div1;
	let t3;
	let style0;
	let t4;
	let t5;
	let style1;
	let t6;
	let t7;
	let div14;
	let div13;
	let div12;
	let div9;
	let div3;
	let h40;
	let t8;
	let t9;
	let p0;
	let t10;
	let t11;
	let form;
	let div6;
	let div5;
	let div4;
	let label;
	let t12;
	let t13;
	let input0;
	let t14;
	let input1;
	let t15;
	let div8;
	let button0;
	let t16;
	let t17;
	let button1;
	let div7;
	let t18;
	let span;
	let t19;
	let t20;
	let input2;
	let t21;
	let div11;
	let div10;
	let h41;
	let t22;
	let t23;
	let p1;
	let t24;
	let t25;
	let script0;
	let t26;
	let t27;
	let script1;
	let script1_src_value;
	let t28;
	let script2;
	let t29;
	let current;
	let each_value = /*social*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div15 = element("div");
			section = element("section");
			div2 = element("div");
			h2 = element("h2");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div0 = element("div");
			t2 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			style0 = element("style");
			t4 = text("@import url(\"https://assets.mlcdn.com/fonts.css?version=1689246\");");
			t5 = space();
			style1 = element("style");
			t6 = text("/* LOADER */\n    .ml-form-embedSubmitLoad {\n      display: inline-block;\n      width: 20px;\n      height: 20px;\n    }\n\n    .g-recaptcha {\n    transform: scale(1);\n    -webkit-transform: scale(1);\n    transform-origin: 0 0;\n    -webkit-transform-origin: 0 0;\n    height: ;\n    }\n\n    .sr-only {\n      position: absolute;\n      width: 1px;\n      height: 1px;\n      padding: 0;\n      margin: -1px;\n      overflow: hidden;\n      clip: rect(0,0,0,0);\n      border: 0;\n    }\n\n    .ml-form-embedSubmitLoad:after {\n      content: \" \";\n      display: block;\n      width: 11px;\n      height: 11px;\n      margin: 1px;\n      border-radius: 50%;\n      border: 4px solid #fff;\n    border-color: #ffffff #ffffff #ffffff transparent;\n    animation: ml-form-embedSubmitLoad 1.2s linear infinite;\n    }\n    @keyframes ml-form-embedSubmitLoad {\n      0% {\n      transform: rotate(0deg);\n      }\n      100% {\n      transform: rotate(360deg);\n      }\n    }\n      #mlb2-6312828.ml-form-embedContainer {\n        box-sizing: border-box;\n        display: table;\n        margin: 0 auto;\n        position: static;\n        width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer h4,\n      #mlb2-6312828.ml-form-embedContainer p,\n      #mlb2-6312828.ml-form-embedContainer span,\n      #mlb2-6312828.ml-form-embedContainer button {\n        text-transform: none !important;\n        letter-spacing: normal !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper {\n        background-color: #f6f6f6;\n        \n        border-width: 0px;\n        border-color: transparent;\n        border-radius: 4px;\n        border-style: solid;\n        box-sizing: border-box;\n        display: inline-block !important;\n        margin: 0;\n        padding: 0;\n        position: relative;\n              }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedPopup,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedDefault { width: 400px; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedForm { max-width: 400px; width: 100%; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-left { text-align: left; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-center { text-align: center; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-default { display: table-cell !important; vertical-align: middle !important; text-align: center !important; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-right { text-align: right; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedHeader img {\n        border-top-left-radius: 4px;\n        border-top-right-radius: 4px;\n        height: auto;\n        margin: 0 auto !important;\n        max-width: 100%;\n        width: undefinedpx;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody {\n        padding: 20px 20px 0 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody.ml-form-embedBodyHorizontal {\n        padding-bottom: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent {\n        text-align: left;\n        margin: 0 0 20px 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent h4,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent h4 {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 30px;\n        font-weight: 400;\n        margin: 0 0 10px 0;\n        text-align: left;\n        word-break: break-word;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        font-weight: 400;\n        line-height: 20px;\n        margin: 0 0 10px 0;\n        text-align: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol {\n        list-style-type: lower-alpha;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol ol {\n        list-style-type: lower-roman;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p a,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p a {\n        color: #000000;\n        text-decoration: underline;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group {\n        text-align: left!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group label {\n        margin-bottom: 5px;\n        color: #333333;\n        font-size: 14px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-weight: bold; font-style: normal; text-decoration: none;;\n        display: inline-block;\n        line-height: 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p:last-child,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody form {\n        margin: 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        margin: 0 0 20px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent.horozintalForm {\n        margin: 0;\n        padding: 0 0 20px 0;\n        width: 100%;\n        height: auto;\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow {\n        margin: 0 0 10px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-last-item {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-formfieldHorizintal {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        margin-left: 0;\n        margin-right: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-webkit-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-webkit-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-ms-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-ms-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow textarea, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow textarea {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          border-color: #cccccc!important;\n          background-color: #ffffff!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input.custom-control-input[type=\"checkbox\"]{\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n        border-radius: 4px!important;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 8 8'%3e%3cpath fill='%23fff' d='M6.564.75l-3.59 3.612-1.538-1.55L0 4.26 2.974 7.25 8 2.193z'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='-4 -4 8 8'%3e%3ccircle r='3' fill='%23fff'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::before  {\n          border-color: #000000!important;\n          background-color: #000000!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::after {\n           top: 2px;\n           box-sizing: border-box;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n           top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n        top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n       #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after {\n            top: 0px!important;\n            box-sizing: border-box!important;\n            position: absolute;\n            left: -1.5rem;\n            display: block;\n            width: 1rem;\n            height: 1rem;\n            content: \"\";\n       }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before {\n        top: 0px!important;\n        box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::after {\n          position: absolute;\n          top: 2px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-radio .custom-control-label::after {\n          background: no-repeat 50%/50% 50%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          background: no-repeat 50%/50% 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-control, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-control {\n        position: relative;\n        display: block;\n        min-height: 1.5rem;\n        padding-left: 1.5rem;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input {\n          position: absolute;\n          z-index: -1;\n          opacity: 0;\n          box-sizing: border-box;\n          padding: 0;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label {\n          color: #000000;\n          font-size: 12px!important;\n          font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n          line-height: 22px;\n          margin-bottom: 0;\n          position: relative;\n          vertical-align: top;\n          font-style: normal;\n          font-weight: 700;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-select, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-select {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        line-height: 20px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 28px 10px 12px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n        height: auto;\n        display: inline-block;\n        vertical-align: middle;\n        background: url('https://assets.mlcdn.com/ml/images/default/dropdown.svg') no-repeat right .75rem center/8px 10px;\n        -webkit-appearance: none;\n        -moz-appearance: none;\n        appearance: none;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow {\n        height: auto;\n        width: 100%;\n        float: left;\n      }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 70%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal { width: 30%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal.labelsOn { padding-top: 25px;  }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .horizontal-fields { box-sizing: border-box; float: left; padding-right: 10px;  }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input {\n        background-color: #ffffff;\n        color: #333333;\n        border-color: #cccccc;\n        border-radius: 4px;\n        border-style: solid;\n        border-width: 1px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        line-height: 20px;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px;\n        width: 100%;\n        box-sizing: border-box;\n        overflow-y: initial;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button {\n        background-color: #004700 !important;\n        border-color: #004700;\n        border-style: solid;\n        border-width: 1px;\n        border-radius: 4px;\n        box-shadow: none;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        font-weight: 700;\n        line-height: 20px;\n        margin: 0 !important;\n        padding: 10px !important;\n        width: 100%;\n        height: auto;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button:hover {\n        background-color: #333333 !important;\n        border-color: #333333 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=\"checkbox\"] {\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description {\n        color: #000000;\n        display: block;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 12px;\n        text-align: left;\n        margin-bottom: 0;\n        position: relative;\n        vertical-align: top;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label {\n        font-weight: normal;\n        margin: 0;\n        padding: 0;\n        position: relative;\n        display: block;\n        min-height: 24px;\n        padding-left: 24px;\n\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label a {\n        color: #000000;\n        text-decoration: underline;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p {\n        color: #000000 !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 12px !important;\n        font-weight: normal !important;\n        line-height: 18px !important;\n        padding: 0 !important;\n        margin: 0 5px 0 0 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit {\n        margin: 0 0 20px 0;\n        float: left;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button {\n        background-color: #027648 !important;\n        border: none !important;\n        border-radius: 4px !important;\n        box-shadow: none !important;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 14px !important;\n        font-weight: 700 !important;\n        line-height: 21px !important;\n        height: auto;\n        padding: 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button.loading {\n        display: none;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button:hover {\n        background-color: #333333 !important;\n      }\n      .ml-subscribe-close {\n        width: 30px;\n        height: 30px;\n        background: url('https://assets.mlcdn.com/ml/images/default/modal_close.png') no-repeat;\n        background-size: 30px;\n        cursor: pointer;\n        margin-top: -10px;\n        margin-right: -10px;\n        position: absolute;\n        top: 0;\n        right: 0;\n      }\n      .ml-error input, .ml-error textarea, .ml-error select {\n        border-color: red!important;\n      }\n\n      .ml-error .custom-checkbox-radio-list {\n        border: 1px solid red !important;\n        border-radius: 4px;\n        padding: 10px;\n      }\n\n      .ml-error .label-description,\n      .ml-error .label-description p,\n      .ml-error .label-description p a,\n      .ml-error label:first-child {\n        color: #ff0000 !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p:first-letter {\n        color: #ff0000 !important;\n      }\n            @media only screen and (max-width: 400px){\n\n        .ml-form-embedWrapper.embedDefault, .ml-form-embedWrapper.embedPopup { width: 100%!important; }\n        .ml-form-formContent.horozintalForm { float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow { height: auto!important; width: 100%!important; float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal > div { padding-right: 0px!important; padding-bottom: 10px; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal.labelsOn { padding-top: 0px!important; }\n\n      }");
			t7 = space();
			div14 = element("div");
			div13 = element("div");
			div12 = element("div");
			div9 = element("div");
			div3 = element("div");
			h40 = element("h4");
			t8 = text("Newsletter");
			t9 = space();
			p0 = element("p");
			t10 = text("Join our newsletter for updates on Zoning Bylaw Renewal and events.");
			t11 = space();
			form = element("form");
			div6 = element("div");
			div5 = element("div");
			div4 = element("div");
			label = element("label");
			t12 = text("Email");
			t13 = space();
			input0 = element("input");
			t14 = space();
			input1 = element("input");
			t15 = space();
			div8 = element("div");
			button0 = element("button");
			t16 = text("Subscribe");
			t17 = space();
			button1 = element("button");
			div7 = element("div");
			t18 = space();
			span = element("span");
			t19 = text("Loading...");
			t20 = space();
			input2 = element("input");
			t21 = space();
			div11 = element("div");
			div10 = element("div");
			h41 = element("h4");
			t22 = text("Thank you!");
			t23 = space();
			p1 = element("p");
			t24 = text("You have successfully joined our subscriber list.");
			t25 = space();
			script0 = element("script");
			t26 = text("function ml_webform_success_6312828() {\n      var $ = ml_jQuery || jQuery;\n      $('.ml-subscribe-form-6312828 .row-success').show();\n      $('.ml-subscribe-form-6312828 .row-form').hide();\n    }");
			t27 = space();
			script1 = element("script");
			t28 = space();
			script2 = element("script");
			t29 = text("fetch(\"https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/track-view\")");
			this.h();
		},
		l(nodes) {
			div15 = claim_element(nodes, "DIV", { class: true, id: true });
			var div15_nodes = children(div15);
			section = claim_element(div15_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h2 = claim_element(div2_nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t0 = claim_text(h2_nodes, /*heading*/ ctx[0]);
			h2_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t2 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(section_nodes);
			style0 = claim_element(section_nodes, "STYLE", { type: true });
			var style0_nodes = children(style0);
			t4 = claim_text(style0_nodes, "@import url(\"https://assets.mlcdn.com/fonts.css?version=1689246\");");
			style0_nodes.forEach(detach);
			t5 = claim_space(section_nodes);
			style1 = claim_element(section_nodes, "STYLE", { type: true });
			var style1_nodes = children(style1);
			t6 = claim_text(style1_nodes, "/* LOADER */\n    .ml-form-embedSubmitLoad {\n      display: inline-block;\n      width: 20px;\n      height: 20px;\n    }\n\n    .g-recaptcha {\n    transform: scale(1);\n    -webkit-transform: scale(1);\n    transform-origin: 0 0;\n    -webkit-transform-origin: 0 0;\n    height: ;\n    }\n\n    .sr-only {\n      position: absolute;\n      width: 1px;\n      height: 1px;\n      padding: 0;\n      margin: -1px;\n      overflow: hidden;\n      clip: rect(0,0,0,0);\n      border: 0;\n    }\n\n    .ml-form-embedSubmitLoad:after {\n      content: \" \";\n      display: block;\n      width: 11px;\n      height: 11px;\n      margin: 1px;\n      border-radius: 50%;\n      border: 4px solid #fff;\n    border-color: #ffffff #ffffff #ffffff transparent;\n    animation: ml-form-embedSubmitLoad 1.2s linear infinite;\n    }\n    @keyframes ml-form-embedSubmitLoad {\n      0% {\n      transform: rotate(0deg);\n      }\n      100% {\n      transform: rotate(360deg);\n      }\n    }\n      #mlb2-6312828.ml-form-embedContainer {\n        box-sizing: border-box;\n        display: table;\n        margin: 0 auto;\n        position: static;\n        width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer h4,\n      #mlb2-6312828.ml-form-embedContainer p,\n      #mlb2-6312828.ml-form-embedContainer span,\n      #mlb2-6312828.ml-form-embedContainer button {\n        text-transform: none !important;\n        letter-spacing: normal !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper {\n        background-color: #f6f6f6;\n        \n        border-width: 0px;\n        border-color: transparent;\n        border-radius: 4px;\n        border-style: solid;\n        box-sizing: border-box;\n        display: inline-block !important;\n        margin: 0;\n        padding: 0;\n        position: relative;\n              }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedPopup,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedDefault { width: 400px; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper.embedForm { max-width: 400px; width: 100%; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-left { text-align: left; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-center { text-align: center; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-default { display: table-cell !important; vertical-align: middle !important; text-align: center !important; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-align-right { text-align: right; }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedHeader img {\n        border-top-left-radius: 4px;\n        border-top-right-radius: 4px;\n        height: auto;\n        margin: 0 auto !important;\n        max-width: 100%;\n        width: undefinedpx;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody {\n        padding: 20px 20px 0 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody.ml-form-embedBodyHorizontal {\n        padding-bottom: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent {\n        text-align: left;\n        margin: 0 0 20px 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent h4,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent h4 {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 30px;\n        font-weight: 400;\n        margin: 0 0 10px 0;\n        text-align: left;\n        word-break: break-word;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        font-weight: 400;\n        line-height: 20px;\n        margin: 0 0 10px 0;\n        text-align: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ul,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol {\n        color: #000000;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol {\n        list-style-type: lower-alpha;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent ol ol ol,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent ol ol ol {\n        list-style-type: lower-roman;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p a,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p a {\n        color: #000000;\n        text-decoration: underline;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group {\n        text-align: left!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-block-form .ml-field-group label {\n        margin-bottom: 5px;\n        color: #333333;\n        font-size: 14px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-weight: bold; font-style: normal; text-decoration: none;;\n        display: inline-block;\n        line-height: 20px;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedContent p:last-child,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-successBody .ml-form-successContent p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody form {\n        margin: 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        margin: 0 0 20px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow {\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-formContent.horozintalForm {\n        margin: 0;\n        padding: 0 0 20px 0;\n        width: 100%;\n        height: auto;\n        float: left;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow {\n        margin: 0 0 10px 0;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-last-item {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow.ml-formfieldHorizintal {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        margin-left: 0;\n        margin-right: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-webkit-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-webkit-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input::-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input::-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-ms-input-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-ms-input-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input:-moz-placeholder,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input:-moz-placeholder { color: #333333; }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow textarea, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow textarea {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        height: auto;\n        line-height: 21px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          border-color: #cccccc!important;\n          background-color: #ffffff!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow input.custom-control-input[type=\"checkbox\"]{\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n        border-radius: 4px!important;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 8 8'%3e%3cpath fill='%23fff' d='M6.564.75l-3.59 3.612-1.538-1.55L0 4.26 2.974 7.25 8 2.193z'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::after {\n        background-image: url(\"data:image/svg+xml,%3csvg xmlns='http://www.w3.org/2000/svg' viewBox='-4 -4 8 8'%3e%3ccircle r='3' fill='%23fff'/%3e%3c/svg%3e\");\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input:checked~.custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox input[type=checkbox]:checked~.label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=checkbox]:checked~.label-description::before  {\n          border-color: #000000!important;\n          background-color: #000000!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label::after {\n           top: 2px;\n           box-sizing: border-box;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n           top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n        top: 0px!important;\n           box-sizing: border-box!important;\n      }\n\n       #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after {\n            top: 0px!important;\n            box-sizing: border-box!important;\n            position: absolute;\n            left: -1.5rem;\n            display: block;\n            width: 1rem;\n            height: 1rem;\n            content: \"\";\n       }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before {\n        top: 0px!important;\n        box-sizing: border-box!important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-control-label::after {\n          position: absolute;\n          top: 2px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::before, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::before {\n          position: absolute;\n          top: 4px;\n          left: -1.5rem;\n          display: block;\n          width: 16px;\n          height: 16px;\n          pointer-events: none;\n          content: \"\";\n          background-color: #ffffff;\n          border: #adb5bd solid 1px;\n          border-radius: 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          position: absolute;\n          top: 0px!important;\n          left: -1.5rem;\n          display: block;\n          width: 1rem;\n          height: 1rem;\n          content: \"\";\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-radio .custom-control-label::after {\n          background: no-repeat 50%/50% 50%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .custom-checkbox .custom-control-label::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedPermissions .ml-form-embedPermissionsOptionsCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-interestGroupsRow .ml-form-interestGroupsRowCheckbox .label-description::after, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description::after {\n          background: no-repeat 50%/50% 50%;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-control, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-control {\n        position: relative;\n        display: block;\n        min-height: 1.5rem;\n        padding-left: 1.5rem;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-input, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-input {\n          position: absolute;\n          z-index: -1;\n          opacity: 0;\n          box-sizing: border-box;\n          padding: 0;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-radio .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-checkbox .custom-control-label, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-checkbox .custom-control-label {\n          color: #000000;\n          font-size: 12px!important;\n          font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n          line-height: 22px;\n          margin-bottom: 0;\n          position: relative;\n          vertical-align: top;\n          font-style: normal;\n          font-weight: 700;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-fieldRow .custom-select, #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow .custom-select {\n        background-color: #ffffff !important;\n        color: #333333 !important;\n        border-color: #cccccc;\n        border-radius: 4px !important;\n        border-style: solid !important;\n        border-width: 1px !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        line-height: 20px !important;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 28px 10px 12px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n        max-width: 100% !important;\n        height: auto;\n        display: inline-block;\n        vertical-align: middle;\n        background: url('https://assets.mlcdn.com/ml/images/default/dropdown.svg') no-repeat right .75rem center/8px 10px;\n        -webkit-appearance: none;\n        -moz-appearance: none;\n        appearance: none;\n      }\n\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow {\n        height: auto;\n        width: 100%;\n        float: left;\n      }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 70%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal { width: 30%; float: left; }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-button-horizontal.labelsOn { padding-top: 25px;  }\n      .ml-form-formContent.horozintalForm .ml-form-horizontalRow .horizontal-fields { box-sizing: border-box; float: left; padding-right: 10px;  }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow input {\n        background-color: #ffffff;\n        color: #333333;\n        border-color: #cccccc;\n        border-radius: 4px;\n        border-style: solid;\n        border-width: 1px;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px;\n        line-height: 20px;\n        margin-bottom: 0;\n        margin-top: 0;\n        padding: 10px 10px;\n        width: 100%;\n        box-sizing: border-box;\n        overflow-y: initial;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button {\n        background-color: #004700 !important;\n        border-color: #004700;\n        border-style: solid;\n        border-width: 1px;\n        border-radius: 4px;\n        box-shadow: none;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 14px !important;\n        font-weight: 700;\n        line-height: 20px;\n        margin: 0 !important;\n        padding: 10px !important;\n        width: 100%;\n        height: auto;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-horizontalRow button:hover {\n        background-color: #333333 !important;\n        border-color: #333333 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow input[type=\"checkbox\"] {\n        box-sizing: border-box;\n        padding: 0;\n        position: absolute;\n        z-index: -1;\n        opacity: 0;\n        margin-top: 5px;\n        margin-left: -1.5rem;\n        overflow: visible;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow .label-description {\n        color: #000000;\n        display: block;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif;\n        font-size: 12px;\n        text-align: left;\n        margin-bottom: 0;\n        position: relative;\n        vertical-align: top;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label {\n        font-weight: normal;\n        margin: 0;\n        padding: 0;\n        position: relative;\n        display: block;\n        min-height: 24px;\n        padding-left: 24px;\n\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label a {\n        color: #000000;\n        text-decoration: underline;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p {\n        color: #000000 !important;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 12px !important;\n        font-weight: normal !important;\n        line-height: 18px !important;\n        padding: 0 !important;\n        margin: 0 5px 0 0 !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow label p:last-child {\n        margin: 0;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit {\n        margin: 0 0 20px 0;\n        float: left;\n        width: 100%;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button {\n        background-color: #027648 !important;\n        border: none !important;\n        border-radius: 4px !important;\n        box-shadow: none !important;\n        color: #ffffff !important;\n        cursor: pointer;\n        font-family: 'Open Sans', Arial, Helvetica, sans-serif !important;\n        font-size: 14px !important;\n        font-weight: 700 !important;\n        line-height: 21px !important;\n        height: auto;\n        padding: 10px !important;\n        width: 100% !important;\n        box-sizing: border-box !important;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button.loading {\n        display: none;\n      }\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-embedSubmit button:hover {\n        background-color: #333333 !important;\n      }\n      .ml-subscribe-close {\n        width: 30px;\n        height: 30px;\n        background: url('https://assets.mlcdn.com/ml/images/default/modal_close.png') no-repeat;\n        background-size: 30px;\n        cursor: pointer;\n        margin-top: -10px;\n        margin-right: -10px;\n        position: absolute;\n        top: 0;\n        right: 0;\n      }\n      .ml-error input, .ml-error textarea, .ml-error select {\n        border-color: red!important;\n      }\n\n      .ml-error .custom-checkbox-radio-list {\n        border: 1px solid red !important;\n        border-radius: 4px;\n        padding: 10px;\n      }\n\n      .ml-error .label-description,\n      .ml-error .label-description p,\n      .ml-error .label-description p a,\n      .ml-error label:first-child {\n        color: #ff0000 !important;\n      }\n\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p,\n      #mlb2-6312828.ml-form-embedContainer .ml-form-embedWrapper .ml-form-embedBody .ml-form-checkboxRow.ml-error .label-description p:first-letter {\n        color: #ff0000 !important;\n      }\n            @media only screen and (max-width: 400px){\n\n        .ml-form-embedWrapper.embedDefault, .ml-form-embedWrapper.embedPopup { width: 100%!important; }\n        .ml-form-formContent.horozintalForm { float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow { height: auto!important; width: 100%!important; float: left!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-form-horizontalRow .ml-input-horizontal > div { padding-right: 0px!important; padding-bottom: 10px; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal { width: 100%!important; }\n        .ml-form-formContent.horozintalForm .ml-button-horizontal.labelsOn { padding-top: 0px!important; }\n\n      }");
			style1_nodes.forEach(detach);
			t7 = claim_space(section_nodes);
			div14 = claim_element(section_nodes, "DIV", { id: true, class: true });
			var div14_nodes = children(div14);
			div13 = claim_element(div14_nodes, "DIV", { class: true });
			var div13_nodes = children(div13);
			div12 = claim_element(div13_nodes, "DIV", { class: true });
			var div12_nodes = children(div12);
			div9 = claim_element(div12_nodes, "DIV", { class: true });
			var div9_nodes = children(div9);
			div3 = claim_element(div9_nodes, "DIV", { class: true, style: true });
			var div3_nodes = children(div3);
			h40 = claim_element(div3_nodes, "H4", {});
			var h40_nodes = children(h40);
			t8 = claim_text(h40_nodes, "Newsletter");
			h40_nodes.forEach(detach);
			t9 = claim_space(div3_nodes);
			p0 = claim_element(div3_nodes, "P", {});
			var p0_nodes = children(p0);
			t10 = claim_text(p0_nodes, "Join our newsletter for updates on Zoning Bylaw Renewal and events.");
			p0_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			t11 = claim_space(div9_nodes);

			form = claim_element(div9_nodes, "FORM", {
				class: true,
				action: true,
				"data-code": true,
				method: true,
				target: true
			});

			var form_nodes = children(form);
			div6 = claim_element(form_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			label = claim_element(div4_nodes, "LABEL", { for: true });
			var label_nodes = children(label);
			t12 = claim_text(label_nodes, "Email");
			label_nodes.forEach(detach);
			t13 = claim_space(div4_nodes);

			input0 = claim_element(div4_nodes, "INPUT", {
				id: true,
				"aria-label": true,
				"aria-required": true,
				type: true,
				class: true,
				"data-inputmask": true,
				name: true,
				placeholder: true,
				autocomplete: true
			});

			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			t14 = claim_space(form_nodes);
			input1 = claim_element(form_nodes, "INPUT", { type: true, name: true });
			t15 = claim_space(form_nodes);
			div8 = claim_element(form_nodes, "DIV", { class: true });
			var div8_nodes = children(div8);
			button0 = claim_element(div8_nodes, "BUTTON", { type: true, class: true });
			var button0_nodes = children(button0);
			t16 = claim_text(button0_nodes, "Subscribe");
			button0_nodes.forEach(detach);
			t17 = claim_space(div8_nodes);
			button1 = claim_element(div8_nodes, "BUTTON", { style: true, type: true, class: true });
			var button1_nodes = children(button1);
			div7 = claim_element(button1_nodes, "DIV", { class: true });
			children(div7).forEach(detach);
			t18 = claim_space(button1_nodes);
			span = claim_element(button1_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t19 = claim_text(span_nodes, "Loading...");
			span_nodes.forEach(detach);
			button1_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			t20 = claim_space(form_nodes);
			input2 = claim_element(form_nodes, "INPUT", { type: true, name: true });
			form_nodes.forEach(detach);
			div9_nodes.forEach(detach);
			t21 = claim_space(div12_nodes);
			div11 = claim_element(div12_nodes, "DIV", { class: true, style: true });
			var div11_nodes = children(div11);
			div10 = claim_element(div11_nodes, "DIV", { class: true });
			var div10_nodes = children(div10);
			h41 = claim_element(div10_nodes, "H4", {});
			var h41_nodes = children(h41);
			t22 = claim_text(h41_nodes, "Thank you!");
			h41_nodes.forEach(detach);
			t23 = claim_space(div10_nodes);
			p1 = claim_element(div10_nodes, "P", {});
			var p1_nodes = children(p1);
			t24 = claim_text(p1_nodes, "You have successfully joined our subscriber list.");
			p1_nodes.forEach(detach);
			div10_nodes.forEach(detach);
			div11_nodes.forEach(detach);
			div12_nodes.forEach(detach);
			div13_nodes.forEach(detach);
			div14_nodes.forEach(detach);
			t25 = claim_space(section_nodes);
			script0 = claim_element(section_nodes, "SCRIPT", {});
			var script0_nodes = children(script0);
			t26 = claim_text(script0_nodes, "function ml_webform_success_6312828() {\n      var $ = ml_jQuery || jQuery;\n      $('.ml-subscribe-form-6312828 .row-success').show();\n      $('.ml-subscribe-form-6312828 .row-form').hide();\n    }");
			script0_nodes.forEach(detach);
			t27 = claim_space(section_nodes);
			script1 = claim_element(section_nodes, "SCRIPT", { src: true, type: true });
			var script1_nodes = children(script1);
			script1_nodes.forEach(detach);
			t28 = claim_space(section_nodes);
			script2 = claim_element(section_nodes, "SCRIPT", {});
			var script2_nodes = children(script2);
			t29 = claim_text(script2_nodes, "fetch(\"https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/track-view\")");
			script2_nodes.forEach(detach);
			section_nodes.forEach(detach);
			div15_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "heading");
			attr(div0, "class", "body svelte-1mgn2yk");
			attr(div1, "class", "social-links svelte-1mgn2yk");
			attr(div2, "class", "content svelte-1mgn2yk");
			attr(style0, "type", "text/css");
			attr(style1, "type", "text/css");
			attr(div3, "class", "ml-form-embedContent");
			attr(div3, "style", "");
			attr(label, "for", "subscribe-to-list");
			attr(input0, "id", "subscribe-to-list");
			attr(input0, "aria-label", "email");
			attr(input0, "aria-required", "true");
			attr(input0, "type", "email");
			attr(input0, "class", "form-control");
			attr(input0, "data-inputmask", "");
			attr(input0, "name", "fields[email]");
			attr(input0, "placeholder", "");
			attr(input0, "autocomplete", "email");
			attr(div4, "class", "ml-field-group ml-field-email ml-validate-email ml-validate-required");
			attr(div5, "class", "ml-form-fieldRow ml-last-item");
			attr(div6, "class", "ml-form-formContent");
			attr(input1, "type", "hidden");
			attr(input1, "name", "ml-submit");
			input1.value = "1";
			attr(button0, "type", "submit");
			attr(button0, "class", "primary");
			attr(div7, "class", "ml-form-embedSubmitLoad");
			attr(span, "class", "sr-only");
			button1.disabled = "disabled";
			set_style(button1, "display", "none");
			attr(button1, "type", "button");
			attr(button1, "class", "loading");
			attr(div8, "class", "ml-form-embedSubmit");
			attr(input2, "type", "hidden");
			attr(input2, "name", "anticsrf");
			input2.value = "true";
			attr(form, "class", "ml-block-form");
			attr(form, "action", "https://assets.mailerlite.com/jsonp/511328/forms/93691462163629222/subscribe");
			attr(form, "data-code", "");
			attr(form, "method", "post");
			attr(form, "target", "_blank");
			attr(div9, "class", "ml-form-embedBody ml-form-embedBodyDefault row-form");
			attr(div10, "class", "ml-form-successContent");
			attr(div11, "class", "ml-form-successBody row-success");
			set_style(div11, "display", "none");
			attr(div12, "class", "ml-form-embedWrapper embedForm");
			attr(div13, "class", "ml-form-align-center ");
			attr(div14, "id", "mlb2-6312828");
			attr(div14, "class", "ml-form-embedContainer ml-subscribe-form ml-subscribe-form-6312828");
			if (!src_url_equal(script1.src, script1_src_value = "https://groot.mailerlite.com/js/w/webforms.min.js?vc2affd81117220f6978e779b988d5128")) attr(script1, "src", script1_src_value);
			attr(script1, "type", "text/javascript");
			attr(section, "class", "section-container svelte-1mgn2yk");
			attr(div15, "class", "section");
			attr(div15, "id", "section-ddb39bbd");
		},
		m(target, anchor) {
			insert_hydration(target, div15, anchor);
			append_hydration(div15, section);
			append_hydration(section, div2);
			append_hydration(div2, h2);
			append_hydration(h2, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div0);
			div0.innerHTML = raw_value;
			append_hydration(div2, t2);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(section, t3);
			append_hydration(section, style0);
			append_hydration(style0, t4);
			append_hydration(section, t5);
			append_hydration(section, style1);
			append_hydration(style1, t6);
			append_hydration(section, t7);
			append_hydration(section, div14);
			append_hydration(div14, div13);
			append_hydration(div13, div12);
			append_hydration(div12, div9);
			append_hydration(div9, div3);
			append_hydration(div3, h40);
			append_hydration(h40, t8);
			append_hydration(div3, t9);
			append_hydration(div3, p0);
			append_hydration(p0, t10);
			append_hydration(div9, t11);
			append_hydration(div9, form);
			append_hydration(form, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, label);
			append_hydration(label, t12);
			append_hydration(div4, t13);
			append_hydration(div4, input0);
			append_hydration(form, t14);
			append_hydration(form, input1);
			append_hydration(form, t15);
			append_hydration(form, div8);
			append_hydration(div8, button0);
			append_hydration(button0, t16);
			append_hydration(div8, t17);
			append_hydration(div8, button1);
			append_hydration(button1, div7);
			append_hydration(button1, t18);
			append_hydration(button1, span);
			append_hydration(span, t19);
			append_hydration(form, t20);
			append_hydration(form, input2);
			append_hydration(div12, t21);
			append_hydration(div12, div11);
			append_hydration(div11, div10);
			append_hydration(div10, h41);
			append_hydration(h41, t22);
			append_hydration(div10, t23);
			append_hydration(div10, p1);
			append_hydration(p1, t24);
			append_hydration(section, t25);
			append_hydration(section, script0);
			append_hydration(script0, t26);
			append_hydration(section, t27);
			append_hydration(section, script1);
			append_hydration(section, t28);
			append_hydration(section, script2);
			append_hydration(script2, t29);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if ((!current || dirty & /*subheading*/ 2) && raw_value !== (raw_value = /*subheading*/ ctx[1].html + "")) div0.innerHTML = raw_value;
			if (dirty & /*social*/ 4) {
				each_value = /*social*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div1, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div15);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;
	let { heading } = $$props;
	let { subheading } = $$props;
	let { social } = $$props;
	let { event } = $$props;

	// Mailerlite
	window.setTimeout(
		() => {
			(function (w, d, e, u, f, l, n) {
				(w[f] = w[f] || function () {
					(w[f].q = w[f].q || []).push(arguments); //ml('account', '511328')
				}, l = d.createElement(e), l.async = 1, l.src = u, n = d.getElementsByTagName(e)[0], n.parentNode.insertBefore(l, n));
			})(window, document, 'script', 'https://assets.mailerlite.com/js/universal.js', 'ml');
		},
		5000
	); //ml('account', '511328')

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(3, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(4, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(6, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(7, preview_image = $$props.preview_image);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('subheading' in $$props) $$invalidate(1, subheading = $$props.subheading);
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
		if ('event' in $$props) $$invalidate(8, event = $$props.event);
	};

	return [
		heading,
		subheading,
		social,
		color1,
		color2,
		favicon,
		title,
		preview_image,
		event
	];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$a, create_fragment$a, safe_not_equal, {
			color1: 3,
			color2: 4,
			favicon: 5,
			title: 6,
			preview_image: 7,
			heading: 0,
			subheading: 1,
			social: 2,
			event: 8
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$b(ctx) {
	let div;
	let iframe;
	let iframe_src_value;

	return {
		c() {
			div = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);

			iframe = claim_element(div_nodes, "IFRAME", {
				id: true,
				title: true,
				src: true,
				width: true,
				height: true,
				style: true,
				class: true
			});

			children(iframe).forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(iframe, "id", "take-action");
			attr(iframe, "title", "Take Action");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://gte-form.vercel.app/")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "width", "100%");
			attr(iframe, "height", "1060px");
			set_style(iframe, "border", "0px");
			set_style(iframe, "overflow", "hidden");
			set_style(iframe, "margin", "auto");
			attr(iframe, "class", "svelte-1o7w9hc");
			attr(div, "class", "section");
			attr(div, "id", "section-dbfc7790");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, iframe);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$b($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(0, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(1, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(4, preview_image = $$props.preview_image);
	};

	return [color1, color2, favicon, title, preview_image];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$b, create_fragment$b, safe_not_equal, {
			color1: 0,
			color2: 1,
			favicon: 2,
			title: 3,
			preview_image: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$c($$self, $$props, $$invalidate) {
	let { color1 } = $$props;
	let { color2 } = $$props;
	let { favicon } = $$props;
	let { title } = $$props;
	let { preview_image } = $$props;

	$$self.$$set = $$props => {
		if ('color1' in $$props) $$invalidate(0, color1 = $$props.color1);
		if ('color2' in $$props) $$invalidate(1, color2 = $$props.color2);
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('preview_image' in $$props) $$invalidate(4, preview_image = $$props.preview_image);
	};

	return [color1, color2, favicon, title, preview_image];
}

class Component$c extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$c, null, safe_not_equal, {
			color1: 0,
			color2: 1,
			favicon: 2,
			title: 3,
			preview_image: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$c(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let t10;
	let component_11;
	let current;

	component_0 = new Component({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				}
			}
		});

	component_1 = new Component$2({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				logo: {
					"image": {
						"alt": "",
						"src": "\thttps://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
						"url": "\thttps://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
						"size": null
					},
					"title": "Grow Together Edmonton"
				},
				site_nav: [
					{
						"link": {
							"url": "/",
							"label": "Home",
							"active": false
						}
					},
					{
						"link": { "url": "/about", "label": "About Us" }
					},
					{
						"link": {
							"url": "/zoning-bylaw",
							"label": "Zoning Bylaw"
						}
					},
					{
						"link": {
							"url": "/#take-action",
							"label": "Take Action"
						}
					}
				],
				logo_width: "100"
			}
		});

	component_2 = new Component$3({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				heading: "Zoning and affordability",
				subhead: "Exclusionary zoning has strangled housing supply and affordability in major cities across Canada. Let's not repeat their mistakes.",
				image: {
					"alt": "",
					"src": "",
					"url": "",
					"size": null
				},
				author: ""
			}
		});

	component_3 = new Component$4({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				content: {
					"html": "<p>According to Rentals.ca, the cost of housing has reached astronomical levels.</p>",
					"markdown": "According to Rentals.ca, the cost of housing has reached astronomical levels."
				},
				data: [
					{
						"city": "Vancouver",
						"rent": "2988",
						"change": "13.1"
					},
					{
						"city": "Toronto",
						"rent": "2610",
						"change": "10.5"
					},
					{
						"city": "Ottawa",
						"rent": "2058",
						"change": "11.0"
					},
					{
						"city": "Calgary",
						"rent": "1728",
						"change": "21.6"
					},
					{
						"city": "Edmonton",
						"rent": "1279",
						"change": "18.0"
					}
				],
				data_source: {
					"url": "https://images.rentals.ca/images/Rent_Report_Graphic_-_August_2023_v1.width-720.png",
					"name": "Rentals.ca August Rent Report"
				}
			}
		});

	component_4 = new Component$5({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				content: {
					"html": "<h3>Rents are reaching crisis levels due to Canada's massive housing shortage</h3><p>In Vancouver, where the vacancy rate is <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://vancouver.citynews.ca/2023/01/26/vancouvers-vacancy-rate-drops/\">under 1%</a>, it now costs more than <strong>$3000/month to rent a 1 bedroom apartment</strong>. In Toronto, it's more than $2500/month. For most young residents, home ownership in these cities is entirely out of reach. Priced out of cities (big and small) across the country, Canadians are moving to Alberta at <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://economicdashboard.alberta.ca/dashboard/net-migration/\">record numbers</a> in search of affordable housing. But if we don't build enough homes to keep up, then we won't stay affordable for very long.</p>",
					"markdown": "### Rents are reaching crisis levels due to Canada's massive housing shortage\n\nIn Vancouver, where the vacancy rate is [under 1%](<https://vancouver.citynews.ca/2023/01/26/vancouvers-vacancy-rate-drops/>), it now costs more than **$3000/month to rent a 1 bedroom apartment**. In Toronto, it's more than $2500/month. For most young residents, home ownership in these cities is entirely out of reach. Priced out of cities (big and small) across the country, Canadians are moving to Alberta at [record numbers](<https://economicdashboard.alberta.ca/dashboard/net-migration/>) in search of affordable housing. But if we don't build enough homes to keep up, then we won't stay affordable for very long.\n\n"
				}
			}
		});

	component_5 = new Component$6({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				image: {
					"alt": "CO2 Usage of Urban and Suburban areas ",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692770626/migration1_xhi-res_f0ntqj.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692770626/migration1_xhi-res_f0ntqj.png",
					"size": null
				},
				max_height: "400",
				caption: { "html": "", "markdown": "" }
			}
		});

	component_6 = new Component$7({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				content: {
					"html": "<p>In fact, housing costs here have already started to surge. In Calgary, the average rent for a 1 bedroom apartment is now up to $1718/month—that's about 3 weeks of pre-tax earnings for a full time minimum wage worker. And in just the past year, <strong>rents in Edmonton have risen 18%</strong> while <a href=\"https://edmontonjournal.com/news/local-news/rents-may-rise-in-edmonton-as-vacancy-rate-hits-10-year-low-affordability-crunched\">our vacancy rate dropped from 7% to 4%, reaching a 10-year low</a>.</p>\n<p>The crux of the issue is that we don't have enough homes. In Canada, <a href=\"https://www150.statcan.gc.ca/t1/tbl1/en/tv.action?pid=3410012601\">we build fewer houses today than we did back in 1976</a> even though <a href=\"https://www.statcan.gc.ca/en/subjects-start/population_and_demography/40-million\">population growth has more than tripled</a>. We have the fewest houses per person <a href=\"https://businesscouncilab.com/insights-category/economic-insights/weekly-econ-minute-canada-housing-shortage/#:~:text=In%20fact%2C%20Canada%20has%20the,480%20dwellings%20per%201%2C000%20residents.\">out of all G7 countries</a>. <a href=\"https://doodles.mountainmath.ca/blog/2019/08/19/running-on-empties/\">There isn't some massive secret supply of vacant homes</a>. Canada just doesn't have enough homes.</p>\n<h3 id=\"relaxingzoningrulesbooststhesupplyofhousingslowingdownrentincreases\">Relaxing zoning rules boosts the supply of housing, slowing down rent increases</h3>\n<p>For decades, zoning bylaws in Canadian cities have outlawed medium density housing by default on the vast majority of residential land. In Edmonton, there are entire neighborhoods where the only infill housing that can feasibly be built <a href=\"https://www.datalabto.ca/a-visual-guide-to-detached-houses-in-5-canadian-cities/\">under our current rules</a> are $600k+ detached/semi-detached houses. To build anything denser would require a long, risky and expensive rezoning process. And even in areas where row houses, multiplexes and small apartments are allowed, they face many onerous restrictions that make them significantly more expensive to build.</p>\n<p>If Edmonton is to remain affordable, then we need to remove barriers to building new homes. That's exactly what <a href=\"https://www.growtogetheryeg.com/zoning-bylaw\">our new zoning bylaw</a> will do, allowing for more homes in more neighborhoods. Here's how this reduces housing costs:</p>\n<ol>\n<li><p>Land for medium density housing will become much less scarce, and therefore cheaper. Combined with a shorter and less risky approval process, many new housing projects will make financial sense to build. This will boost our housing stock, helping to keep rents in check.</p></li>\n<li><p>It will enable more affordable housing options. Not everyone wants or can afford a large detached house, but in many neighborhoods there are few alternatives. The new zoning bylaw will allow rowhouses, multiplexes and small apartments (3 storeys or less) in every neighbourhood.</p></li>\n<li><p>A major contributor to the high price of infill housing is the cost of purchasing land and demolishing existing structures. Our new zoning rules would permit higher density housing, allowing builders to spread those fixed costs over more units with a larger total living space.</p></li>\n</ol>\n<!-- -->\n<h3 id=\"casestudyaucklandnz\">Case Study: Auckland, NZ</h3>\n<p>Auckland, New Zealand is a rare example of a city that undertook zoning reform as as comprehensive as ours. Since upzoning, their housing starts have skyrocketed and their rents stayed flat (adjusted for inflation), even though they rose rapidly in the rest of the country. <a href=\"https://cdn.auckland.ac.nz/assets/business/about/our-research/research-institutes-and-centres/Economic-Policy-Centre--EPC-/006WP%20-%204.pdf\">Sophisticated analysis from the University of Auckland</a> shows that ~21,000 extra homes were built over just 5 years as a direct result of the zoning reform. That’s about 4% of their entire housing supply that only exists because zoning laws in Auckland had been relaxed.</p>",
					"markdown": "In fact, housing costs here have already started to surge. In Calgary, the average rent for a 1 bedroom apartment is now up to $1718/month—that's about 3 weeks of pre-tax earnings for a full time minimum wage worker. And in just the past year, **rents in Edmonton have risen 18%** while [our vacancy rate dropped from 7% to 4%, reaching a 10-year low](<https://edmontonjournal.com/news/local-news/rents-may-rise-in-edmonton-as-vacancy-rate-hits-10-year-low-affordability-crunched>).\n\nThe crux of the issue is that we don't have enough homes. In Canada, [we build fewer houses today than we did back in 1976](<https://www150.statcan.gc.ca/t1/tbl1/en/tv.action?pid=3410012601>) even though [population growth has more than tripled](<https://www.statcan.gc.ca/en/subjects-start/population_and_demography/40-million>). We have the fewest houses per person [out of all G7 countries](<https://businesscouncilab.com/insights-category/economic-insights/weekly-econ-minute-canada-housing-shortage/#:~:text=In%20fact%2C%20Canada%20has%20the,480%20dwellings%20per%201%2C000%20residents.>). [There isn't some massive secret supply of vacant homes](<https://doodles.mountainmath.ca/blog/2019/08/19/running-on-empties/>). Canada just doesn't have enough homes.\n\n### Relaxing zoning rules boosts the supply of housing, slowing down rent increases\n\nFor decades, zoning bylaws in Canadian cities have outlawed medium density housing by default on the vast majority of residential land. In Edmonton, there are entire neighborhoods where the only infill housing that can feasibly be built [under our current rules](<https://www.datalabto.ca/a-visual-guide-to-detached-houses-in-5-canadian-cities/>) are $600k+ detached/semi-detached houses. To build anything denser would require a long, risky and expensive rezoning process. And even in areas where row houses, multiplexes and small apartments are allowed, they face many onerous restrictions that make them significantly more expensive to build.\n\nIf Edmonton is to remain affordable, then we need to remove barriers to building new homes. That's exactly what [our new zoning bylaw](<https://www.growtogetheryeg.com/zoning-bylaw>) will do, allowing for more homes in more neighborhoods. Here's how this reduces housing costs:\n\n1. Land for medium density housing will become much less scarce, and therefore cheaper. Combined with a shorter and less risky approval process, many new housing projects will make financial sense to build. This will boost our housing stock, helping to keep rents in check.\n\n2. It will enable more affordable housing options. Not everyone wants or can afford a large detached house, but in many neighborhoods there are few alternatives. The new zoning bylaw will allow rowhouses, multiplexes and small apartments (3 storeys or less) in every neighbourhood.\n\n3. A major contributor to the high price of infill housing is the cost of purchasing land and demolishing existing structures. Our new zoning rules would permit higher density housing, allowing builders to spread those fixed costs over more units with a larger total living space.\n\n\n<!-- -->\n\n### Case Study: Auckland, NZ\n\nAuckland, New Zealand is a rare example of a city that undertook zoning reform as as comprehensive as ours. Since upzoning, their housing starts have skyrocketed and their rents stayed flat (adjusted for inflation), even though they rose rapidly in the rest of the country. [Sophisticated analysis from the University of Auckland](<https://cdn.auckland.ac.nz/assets/business/about/our-research/research-institutes-and-centres/Economic-Policy-Centre--EPC-/006WP%20-%204.pdf>) shows that \\~21,000 extra homes were built over just 5 years as a direct result of the zoning reform. That’s about 4% of their entire housing supply that only exists because zoning laws in Auckland had been relaxed.\n\n"
				}
			}
		});

	component_7 = new Component$8({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				content: {
					"html": "<p>Here's a graph that shows how rents have changed in Auckland since they updated their zoning bylaw compared to the rest of New Zealand. <a href=\"https://onefinaleffort.com/auckland\">Source</a>\n<img src=\"https://res.cloudinary.com/dbnijop5c/image/upload/f_auto/v1689461104/Screenshot_2023-07-15_164425_iphids.png\" alt=\"Housing Starts\" /></p>",
					"markdown": "Here's a graph that shows how rents have changed in Auckland since they updated their zoning bylaw compared to the rest of New Zealand. [Source](https://onefinaleffort.com/auckland)\n![Housing Starts](https://res.cloudinary.com/dbnijop5c/image/upload/f_auto/v1689461104/Screenshot_2023-07-15_164425_iphids.png)\n"
				}
			}
		});

	component_8 = new Component$9({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				content: {
					"html": "<p>This graph shows how housing starts have skyrocketed in Auckland since they updated their zoning bylaw. <a href=\"https://onefinaleffort.com/auckland\">Source</a>\n<img src=\"https://res.cloudinary.com/dbnijop5c/image/upload/f_auto/v1689461386/auckland-housing-starts_ffjno9.png\" alt=\"Housing Starts\" /></p>",
					"markdown": "This graph shows how housing starts have skyrocketed in Auckland since they updated their zoning bylaw. [Source](https://onefinaleffort.com/auckland)\n![Housing Starts](https://res.cloudinary.com/dbnijop5c/image/upload/f_auto/v1689461386/auckland-housing-starts_ffjno9.png)\n"
				}
			}
		});

	component_9 = new Component$a({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				},
				heading: "Get Involved",
				subheading: {
					"html": "<p>Zoning Bylaw Renewal goes to a public hearing and vote on October 16th and there will be a lot of opposition from NIMBYs.</p><p>Make sure your voice is heard too! We've got a <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link link\" href=\"https://gtyeg.ca/speaking\">step by step guide for signing up for the public hearing</a> and speaking to council.</p>",
					"markdown": "Zoning Bylaw Renewal goes to a public hearing and vote on October 16th and there will be a lot of opposition from NIMBYs.\n\nMake sure your voice is heard too! We've got a [step by step guide for signing up for the public hearing](<https://gtyeg.ca/speaking>) and speaking to council.\n\n"
				},
				social: [
					{
						"icon": "mdi:twitter",
						"link": {
							"url": "https://twitter.com/GrowTogetherYEG",
							"label": "Twitter"
						}
					},
					{
						"icon": "mdi:instagram",
						"link": {
							"url": "https://www.instagram.com/growtogetheryeg/",
							"label": "Instagram"
						}
					},
					{
						"icon": "mdi:discord",
						"link": {
							"url": "https://discord.com/invite/bQsDZ3KWra",
							"label": "Discord"
						}
					}
				],
				event: {
					"link": "https://www.eventbrite.com/e/drinks-for-density-tickets-708836467957?aff=oddtdtcreator",
					"description": "Join us on Sept. 25th for our \"Drinks for Density\" event. "
				}
			}
		});

	component_10 = new Component$b({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				}
			}
		});

	component_11 = new Component$c({
			props: {
				color1: "#A9CD37",
				color2: "",
				favicon: {
					"alt": "Grow Together YEG is an advocacy group pushing for a more sustainable and affordable Edmonton. We support the new Zoning Bylaw.",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692649250/gtyeg_logo_no_text_darker_32_dkly4s.png",
					"size": null
				},
				title: "Zoning and affordability",
				preview_image: {
					"alt": "",
					"src": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"url": "https://res.cloudinary.com/dbnijop5c/image/upload/v1692598023/gtyeg_logo_no_text_darker_kfvwjs.svg",
					"size": null
				}
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
			t10 = space();
			create_component(component_11.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
			t10 = claim_space(nodes);
			claim_component(component_11.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
			insert_hydration(target, t10, anchor);
			mount_component(component_11, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
			transition_in(component_11.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
			transition_out(component_11.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
			if (detaching) detach(t10);
			destroy_component(component_11, detaching);
		}
	};
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$c, safe_not_equal, {});
	}
}

export default Component$d;
