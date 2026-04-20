/* ═══════════════════════════════════════════════════════════════════════════
   NexusSync Enterprise PPM — app.js v3.0
   Full Waterfall Scheduling Engine with CPM Cascade, RBAC, Audit Log,
   Triage Dashboard, Breadcrumb Navigation, & Critical Path Detection
   ═══════════════════════════════════════════════════════════════════════════ */

// ─────────────────────────────────────────────
// DATABASE SCHEMA & STATE (localStorage)
// ─────────────────────────────────────────────
function resetAndSeedData() {
    const db = {
        projects: [],
        milestones: [],
        tasks: [],
        subtasks: [],
        audit_log: [],    // Immutable governance trail (replaces comments)
        templates: []
    };
    localStorage.setItem('nexus_db_v3', JSON.stringify(db));
    return db;
}

// Migrate from old schema if needed
function migrateDb(raw) {
    if (!raw) return null;
    try {
        const d = JSON.parse(raw);
        if (!d.audit_log) {
            // migrate old comments array
            d.audit_log = (d.comments || []).map(c => ({
                id: 'al' + Date.now() + Math.random(),
                itemId: c.itemId,
                itemName: 'Unknown',
                type: c.type || 'Task',
                oldStatus: null,
                newStatus: c.newStatus,
                comment: c.comment,
                role: c.role,
                timestamp: c.timestamp
            }));
            delete d.comments;
        }
        if (!d.templates) d.templates = [];
        if (!d.projects)  d.projects  = [];
        if (!d.milestones) d.milestones = [];
        if (!d.tasks) d.tasks = [];
        if (!d.subtasks) d.subtasks = [];
        return d;
    } catch { return null; }
}

let db = migrateDb(localStorage.getItem('nexus_db_v3'))
      || migrateDb(localStorage.getItem('nexus_db'))
      || resetAndSeedData();

function saveDb() { localStorage.setItem('nexus_db_v3', JSON.stringify(db)); }

let activeRole = 'PORTFOLIO_MANAGER';

// RBAC: visible projects based on role
function visibleProjects() {
    if (activeRole === 'PORTFOLIO_MANAGER') return db.projects;
    return db.projects.filter(p => p.managerId === 'PM_2');
}

// ─────────────────────────────────────────────
// HELPERS
// ─────────────────────────────────────────────
const today = () => new Date().toISOString().split('T')[0];

function genId(prefix) {
    return prefix + Date.now().toString(36) + Math.random().toString(36).slice(2, 6);
}

function daysDiff(dateStr) {
    if (!dateStr) return null;
    return (new Date(dateStr) - new Date(today())) / 86400000;
}

function addDays(dateStr, days) {
    if (!dateStr) return dateStr;
    const d = new Date(dateStr);
    d.setDate(d.getDate() + days);
    return d.toISOString().split('T')[0];
}

function dateDiffDays(dateA, dateB) {
    // returns (dateB - dateA) in integer days
    if (!dateA || !dateB) return 0;
    return Math.round((new Date(dateB) - new Date(dateA)) / 86400000);
}

function getDeadlineColor(planned_end, status) {
    if (status === 'Completed') return 'status-gray';
    if (!planned_end) return 'status-gray';
    const d = daysDiff(planned_end);
    if (d < 0)   return 'status-red';
    if (d <= 3)  return 'status-yellow';
    return 'status-green';
}

function getGanttBarClass(item) {
    if (item.status === 'Completed') return 'gantt-bar-completed';
    if (item.status === 'On hold')   return 'gantt-bar-hold';
    if (item.status === 'Started')   return 'gantt-bar-started';
    const d = daysDiff(item.planned_end);
    if (d !== null && d < 0) return 'gantt-bar-overdue';
    return 'gantt-bar-yet';
}

function priorityBadge(priority) {
    if (!priority) return '';
    const cls = { Critical:'badge-critical', High:'badge-high', Medium:'badge-medium', Low:'badge-low' };
    return `<span class="badge ${cls[priority] || 'badge-medium'}">${priority}</span>`;
}

function progressBar(taskId) {
    const subs = db.subtasks.filter(s => s.taskId === taskId);
    if (!subs.length) return '';
    const pct = Math.round(subs.filter(s => s.status === 'Completed').length / subs.length * 100);
    const col  = pct === 100 ? 'var(--success)' : pct >= 50 ? 'var(--accent-primary)' : 'var(--warning)';
    return `<div class="progress-wrap">
        <div class="progress-bar"><div class="progress-fill" style="width:${pct}%;background:${col}"></div></div>
        <span class="progress-label">${pct}%</span>
    </div>`;
}

function statusPill(status) {
    const map = {
        'Yet to start': 'pill-yet',
        'Started':      'pill-started',
        'On hold':      'pill-hold',
        'Completed':    'pill-done'
    };
    return `<span class="portfolio-status-pill ${map[status] || 'pill-yet'}">${status}</span>`;
}

function showToast(msg, type = 'success') {
    const t = document.getElementById('toast');
    t.innerHTML = (type === 'error' ? '⚠️ ' : '✅ ') + msg;
    t.style.background = type === 'error' ? 'var(--danger)' : 'var(--success)';
    t.style.boxShadow  = type === 'error'
        ? '0 4px 16px rgba(239,68,68,0.3)'
        : '0 4px 16px rgba(16,212,122,0.25)';
    t.classList.remove('hidden');
    clearTimeout(t._tmr);
    t._tmr = setTimeout(() => t.classList.add('hidden'), 3500);
}

// ─────────────────────────────────────────────
// CIRCULAR DEPENDENCY DETECTION
// Returns true if setting predecessor_id = predId on item `id` would
// create a cycle in the same-level dependency graph.
// ─────────────────────────────────────────────
function wouldCreateCycle(collection, id, predId) {
    if (!predId || predId === id) return predId === id;
    // Walk up the predecessor chain from predId
    const visited = new Set();
    let cur = predId;
    while (cur) {
        if (cur === id) return true;
        if (visited.has(cur)) return true; // already a cycle somewhere
        visited.add(cur);
        const node = collection.find(x => x.id === cur);
        cur = node ? node.predecessor_id : null;
    }
    return false;
}

// ─────────────────────────────────────────────
// TEMPORAL ENVELOPE VALIDATION
// child dates must fall within parent dates
// ─────────────────────────────────────────────
function validateTemporalEnvelope(type, parentId, startDate, endDate) {
    let parent = null;
    if (type === 'Milestone') parent = db.projects.find(p => p.id === parentId);
    else if (type === 'Task') parent = db.milestones.find(m => m.id === parentId);
    else if (type === 'Subtask') parent = db.tasks.find(t => t.id === parentId);

    if (!parent || !parent.planned_start || !parent.planned_end) return null; // no constraint
    if (startDate && new Date(startDate) < new Date(parent.planned_start)) {
        return `Start date cannot be before parent ${type === 'Milestone' ? 'Project' : type === 'Task' ? 'Milestone' : 'Task'} start (${parent.planned_start})`;
    }
    if (endDate && new Date(endDate) > new Date(parent.planned_end)) {
        return `End date cannot exceed parent ${type === 'Milestone' ? 'Project' : type === 'Task' ? 'Milestone' : 'Task'} end (${parent.planned_end})`;
    }
    return null;
}

// ─────────────────────────────────────────────
// CASCADE ENGINE — RIPPLE DOWN (Forward Pass CPM)
// Recursively propagates a schedule delay down the dependency chain.
// varianceDays = Δt = actual_end - planned_end (positive = delay)
// ─────────────────────────────────────────────
function propagateDelayCascade(completedId, varianceDays, type) {
    if (!varianceDays || varianceDays <= 0) return;

    const collection = type === 'Task' ? db.tasks
                     : type === 'Subtask' ? db.subtasks
                     : type === 'Milestone' ? db.milestones
                     : null;
    if (!collection) return;

    // Find ALL direct successors (items whose predecessor_id === completedId)
    const successors = collection.filter(x => x.predecessor_id === completedId);

    successors.forEach(succ => {
        succ.planned_start = addDays(succ.planned_start, varianceDays);
        succ.planned_end   = addDays(succ.planned_end,   varianceDays);
        // Recurse: propagate the same variance further down the chain
        propagateDelayCascade(succ.id, varianceDays, type);
    });
}

// ─────────────────────────────────────────────
// CASCADE ENGINE — RIPPLE UP (Status Aggregation)
// Auto-start parent when first child starts; auto-complete parent when
// all children are complete.
// ─────────────────────────────────────────────
function bubbleUp(parentType, parentId, childColl, matchField) {
    const collMap = { Project: db.projects, Milestone: db.milestones, Task: db.tasks };
    const parent = collMap[parentType]?.find(p => p.id === parentId);
    if (!parent) return;

    const children = childColl.filter(c => c[matchField] === parentId);
    const prev = parent.status;

    const allDone = children.length > 0 && children.every(c => c.status === 'Completed');
    const anyActive = children.some(c => c.status === 'Started' || c.status === 'Completed');

    if (allDone && parent.status !== 'Completed') {
        const oldStatus = parent.status;
        parent.status = 'Completed';
        parent.actual_end = today();
        // Cascade the parent's own completion variance downward as well
        const variance = dateDiffDays(parent.planned_end, parent.actual_end);
        if (variance > 0) propagateDelayCascade(parent.id, variance, parentType);
        // Write auto-completed audit entry
        _writeAuditEntry(parent.id, parent.name, parentType, oldStatus, 'Completed',
            `[Auto-completed] All child items finished.`);
    } else if (anyActive && parent.status === 'Yet to start') {
        parent.status = 'Started';
        parent.actual_start = today();
        _writeAuditEntry(parent.id, parent.name, parentType, 'Yet to start', 'Started',
            `[Auto-started] First child item became active.`);
    }

    // Recurse upward if changed
    if (parent.status !== prev) {
        if (parentType === 'Task')      bubbleUp('Milestone', parent.milestoneId, db.tasks, 'milestoneId');
        if (parentType === 'Milestone') bubbleUp('Project',   parent.projectId,   db.milestones, 'projectId');
    }
}

// Internal: write audit log entry (also used by auto-triggers)
function _writeAuditEntry(itemId, itemName, type, oldStatus, newStatus, comment, role) {
    db.audit_log.unshift({
        id:        genId('al'),
        itemId,
        itemName:  itemName || '(unknown)',
        type,
        oldStatus,
        newStatus,
        comment:   comment || '',
        role:      role || 'System',
        timestamp: new Date().toISOString()
    });
}

// ─────────────────────────────────────────────
// UPDATE ITEM STATUS (called from status form submit)
// ─────────────────────────────────────────────
function updateItemStatus(id, type, newStatus, comment) {
    const collMap = {
        Project:   db.projects,
        Milestone: db.milestones,
        Task:      db.tasks,
        Subtask:   db.subtasks
    };
    const collection = collMap[type];
    const item = collection?.find(i => i.id === id);
    if (!item) return;

    const oldStatus = item.status;

    // Stamp actual dates
    if (newStatus === 'Started' && item.status !== 'Started') {
        item.actual_start = today();
    }

    item.status = newStatus;

    if (newStatus === 'Completed') {
        item.actual_end = today();
        // Ripple Down — calculate variance and cascade
        const variance = dateDiffDays(item.planned_end, item.actual_end);
        if (variance > 0) {
            propagateDelayCascade(item.id, variance, type);
        }
    }

    // Write immutable audit entry
    const role = activeRole === 'PORTFOLIO_MANAGER' ? 'Portfolio Manager' : 'Project Manager';
    _writeAuditEntry(id, item.name, type, oldStatus, newStatus, comment, role);

    // Ripple Up
    if (type === 'Subtask')   bubbleUp('Task',      item.taskId,      db.subtasks,  'taskId');
    if (type === 'Task')      bubbleUp('Milestone',  item.milestoneId, db.tasks,     'milestoneId');
    if (type === 'Milestone') bubbleUp('Project',    item.projectId,   db.milestones,'projectId');
}

// ─────────────────────────────────────────────
// DELETE WITH CASCADE
// ─────────────────────────────────────────────
window.confirmDelete = (id, type, name) => {
    const msg = document.getElementById('confirm-msg');
    msg.innerHTML = `Delete <strong>${type}: "${name}"</strong>?<br>
        <span style="font-size:11px;color:var(--danger)">⚠️ This permanently removes the item and all its children.</span>`;
    document.getElementById('confirm-modal').classList.remove('hidden');
    document.getElementById('confirm-ok-btn').onclick = () => {
        deleteItem(id, type);
        document.getElementById('confirm-modal').classList.add('hidden');
        saveDb();
        renderApp();
        showToast(`${type} "${name}" deleted`);
    };
};

function deleteItem(id, type) {
    if (type === 'Project') {
        const mIds = db.milestones.filter(m => m.projectId === id).map(m => m.id);
        mIds.forEach(mid => deleteItem(mid, 'Milestone'));
        db.projects = db.projects.filter(p => p.id !== id);
    } else if (type === 'Milestone') {
        const tIds = db.tasks.filter(t => t.milestoneId === id).map(t => t.id);
        tIds.forEach(tid => deleteItem(tid, 'Task'));
        db.milestones = db.milestones.filter(m => m.id !== id);
        // Clear predecessor references
        db.milestones.forEach(m => { if (m.predecessor_id === id) m.predecessor_id = null; });
    } else if (type === 'Task') {
        db.subtasks = db.subtasks.filter(s => s.taskId !== id);
        db.tasks = db.tasks.filter(t => t.id !== id);
        // Clear predecessor references
        db.tasks.forEach(t => { if (t.predecessor_id === id) t.predecessor_id = null; });
    } else if (type === 'Subtask') {
        db.subtasks = db.subtasks.filter(s => s.id !== id);
        db.subtasks.forEach(s => { if (s.predecessor_id === id) s.predecessor_id = null; });
    }
    // Remove audit entries for this item
    db.audit_log = db.audit_log.filter(a => a.itemId !== id);
}

// ─────────────────────────────────────────────
// RENDER APP (main dispatcher)
// ─────────────────────────────────────────────
function renderApp() {
    renderDashboard();
    renderPortfolio();
    renderWorkItems();
    renderKanban();
    renderGantt();
    renderMilestoneTracker();
    renderTemplates();
    renderAuditLog();
    populateGanttSelect();
    populateKanbanSelect();
    populateMilestoneTrackerSelect();
    updateSidebarBadge();
}

function updateSidebarBadge() {
    // Show overdue count on nav badge (if we add one)
    const overdue = [...db.tasks, ...db.subtasks]
        .filter(x => x.status !== 'Completed' && daysDiff(x.planned_end) < 0).length;
    // Could add badge to audit nav item — count new entries
    const auditBtn = document.querySelector('[data-target="audit"]');
    if (auditBtn) {
        const existing = auditBtn.querySelector('.nav-badge');
        if (existing) existing.remove();
        if (overdue > 0) {
            auditBtn.insertAdjacentHTML('beforeend', `<span class="nav-badge">${overdue}</span>`);
        }
    }
}

// ─────────────────────────────────────────────
// BREADCRUMB SYSTEM
// ─────────────────────────────────────────────
let breadcrumbStack = [{ label: '🏠 Home', view: 'dashboard', id: null }];

function setBreadcrumb(stack) {
    breadcrumbStack = stack;
    renderBreadcrumb();
}

function renderBreadcrumb() {
    const bar = document.getElementById('breadcrumb-bar');
    if (!bar) return;
    bar.innerHTML = breadcrumbStack.map((crumb, i) => {
        const isLast = i === breadcrumbStack.length - 1;
        const sep = i > 0 ? `<span class="breadcrumb-sep">›</span>` : '';
        return `${sep}<span class="breadcrumb-item ${isLast ? 'active' : ''}"
            onclick="${isLast ? '' : `jumpBreadcrumb(${i})`}">${crumb.label}</span>`;
    }).join('');
}

window.jumpBreadcrumb = (idx) => {
    breadcrumbStack = breadcrumbStack.slice(0, idx + 1);
    const crumb = breadcrumbStack[idx];
    renderBreadcrumb();
    navTo(crumb.view);
};

function navTo(target) {
    document.querySelectorAll('.nav-item').forEach(b => {
        b.classList.toggle('active', b.getAttribute('data-target') === target);
    });
    document.querySelectorAll('.view-section').forEach(v => {
        v.classList.remove('active');
        v.classList.add('hidden');
    });
    const view = document.getElementById(`view-${target}`);
    if (view) { view.classList.remove('hidden'); view.classList.add('active'); }
    const btn = document.querySelector(`[data-target="${target}"]`);
    document.getElementById('current-view-title').innerText =
        btn ? btn.innerText.replace(/^[^\w📊🗺️🗂️📋📅🏁📄🔴]*/, '').trim() : target;
}

// ─────────────────────────────────────────────
// DASHBOARD
// ─────────────────────────────────────────────
function renderDashboard() {
    const vp = visibleProjects();
    const vpIds = new Set(vp.map(p => p.id));
    const allTasks = db.tasks.filter(t => {
        const ms = db.milestones.find(m => m.id === t.milestoneId);
        return ms && vpIds.has(ms.projectId);
    });
    const allSubs = db.subtasks.filter(s => {
        const tk = db.tasks.find(t => t.id === s.taskId);
        if (!tk) return false;
        const ms = db.milestones.find(m => m.id === tk.milestoneId);
        return ms && vpIds.has(ms.projectId);
    });
    const allItems = [...allTasks, ...allSubs];

    const overdue  = allItems.filter(t => t.status !== 'Completed' && t.planned_end && daysDiff(t.planned_end) < 0);
    const dueSoon  = allItems.filter(t => t.status !== 'Completed' && t.planned_end && daysDiff(t.planned_end) >= 0 && daysDiff(t.planned_end) <= 7);
    const completed = allTasks.filter(t => t.status === 'Completed');
    const runningProjects = vp.filter(p => p.status === 'Started');
    const runningTasks    = allTasks.filter(t => t.status === 'Started');

    // Metric cards
    document.getElementById('metric-projects').innerText  = vp.length;
    document.getElementById('metric-projects-running').innerText = `${runningProjects.length} running`;
    document.getElementById('metric-tasks').innerText     = allTasks.length;
    document.getElementById('metric-tasks-running').innerText   = `${runningTasks.length} running`;
    document.getElementById('metric-subtasks').innerText  = allSubs.length;
    document.getElementById('metric-subtasks-done').innerText   = `${allSubs.filter(s => s.status === 'Completed').length} completed`;
    document.getElementById('metric-overdue').innerText   = overdue.length;
    document.getElementById('metric-due-soon').innerText  = dueSoon.length;
    document.getElementById('metric-completed').innerText = completed.length;

    // ── TRIAGE BUCKETS ──────────────────────────────
    // Green: Completed AND actual_end <= planned_end
    const greenItems = allItems.filter(x =>
        x.status === 'Completed' && x.actual_end && x.planned_end && x.actual_end <= x.planned_end
    );
    // Yellow: NOT completed AND planned_end > today
    const yellowItems = allItems.filter(x =>
        x.status !== 'Completed' && x.planned_end && daysDiff(x.planned_end) > 0
    );
    // Red: NOT completed AND planned_end < today
    const redItems = allItems.filter(x =>
        x.status !== 'Completed' && x.planned_end && daysDiff(x.planned_end) < 0
    );

    document.getElementById('triage-green-count').innerText  = greenItems.length;
    document.getElementById('triage-yellow-count').innerText = yellowItems.length;
    document.getElementById('triage-red-count').innerText    = redItems.length;

    const renderTriageList = (items, maxShow = 5) =>
        items.slice(0, maxShow).map(x =>
            `<div class="triage-item">
                <span class="triage-item-name">${x.name}</span>
                <span class="triage-item-date">${x.planned_end || ''}</span>
            </div>`
        ).join('') + (items.length > maxShow
            ? `<div style="font-size:10px;color:var(--text-secondary);text-align:center;padding:4px">+${items.length - maxShow} more</div>` : '');

    document.getElementById('triage-green-list').innerHTML  = greenItems.length  ? renderTriageList(greenItems)  : '';
    document.getElementById('triage-yellow-list').innerHTML = yellowItems.length ? renderTriageList(yellowItems) : '';
    document.getElementById('triage-red-list').innerHTML    = redItems.length    ? renderTriageList(redItems)    : '';

    // ── RECENT PROJECTS ──────────────────────────────
    const rp = document.getElementById('dashboard-recent-projects');
    rp.innerHTML = vp.length === 0
        ? '<span style="color:var(--text-secondary);font-size:13px">No projects yet.</span>'
        : vp.slice(-5).reverse().map(p => `
            <div class="recent-item">
                <strong style="font-size:13px">${p.name}</strong>
                ${statusPill(p.status)}
            </div>`).join('');

    // ── OVERDUE LIST ──────────────────────────────
    const ol = document.getElementById('dashboard-overdue-list');
    ol.innerHTML = overdue.length === 0
        ? '<span style="color:var(--text-secondary);font-size:13px">🎉 Nothing overdue!</span>'
        : overdue.slice(0, 6).map(t => `
            <div class="overdue-item">
                <span style="font-size:12px">${t.name}</span>
                <span style="color:var(--danger);font-size:10px;font-weight:600">${t.planned_end}</span>
            </div>`).join('');

    // ── UPCOMING ──────────────────────────────
    const ul = document.getElementById('dashboard-upcoming-list');
    ul.innerHTML = dueSoon.length === 0
        ? '<span style="color:var(--text-secondary);font-size:13px">Nothing due this week.</span>'
        : dueSoon.slice(0, 6).map(t => `
            <div class="upcoming-item">
                <span style="font-size:12px">${t.name}</span>
                <span style="color:var(--warning);font-size:10px;font-weight:600">${t.planned_end}</span>
            </div>`).join('');
}

// ─────────────────────────────────────────────
// PORTFOLIO MAP  (text-based milestone string tracker)
// ─────────────────────────────────────────────
function buildMilestoneString(projectId) {
    const milestones = db.milestones
        .filter(m => m.projectId === projectId)
        .sort((a, b) => (a.planned_start || '').localeCompare(b.planned_start || ''));

    if (!milestones.length) return '<span style="color:var(--text-muted);font-size:11px">No milestones yet</span>';

    return milestones.map((m, i) => {
        const sym = m.status === 'Completed' ? `<span class="ms-sym-done">(X)</span>`
                  : m.status === 'Started'   ? `<span class="ms-sym-started">(.)</span>`
                  : `<span class="ms-sym-yet">( )</span>`;
        const name = `<span style="font-size:11px;color:var(--text-secondary)">${m.name}</span>`;
        const arrow = i < milestones.length - 1 ? `<span class="ms-arrow"> ──→ </span>` : '';
        return `${sym} ${name}${arrow}`;
    }).join('');
}

function renderPortfolio() {
    const container = document.getElementById('portfolio-grid');
    const vp = visibleProjects();
    if (!vp.length) {
        container.innerHTML = `<div class="empty-state">
            <div class="empty-state-icon">🗺️</div>
            <div class="empty-state-title">No Projects Yet</div>
            <div>Create your first project to begin tracking.</div>
        </div>`;
        return;
    }

    container.innerHTML = vp.map(p => {
        const mCount = db.milestones.filter(m => m.projectId === p.id).length;
        const tCount = db.tasks.filter(t => {
            const m = db.milestones.find(ms => ms.id === t.milestoneId);
            return m?.projectId === p.id;
        }).length;
        return `<div class="portfolio-card" onclick="drillToProject('${p.id}','${p.name.replace(/'/g,"\\'")}')">
            <div class="portfolio-card-header">
                <div class="portfolio-card-name">${p.name}</div>
                ${statusPill(p.status)}
            </div>
            <div class="milestone-tracker-string">${buildMilestoneString(p.id)}</div>
            <div class="portfolio-meta">
                <span>🏁 ${mCount} milestone${mCount !== 1 ? 's' : ''}</span>
                <span>📋 ${tCount} task${tCount !== 1 ? 's' : ''}</span>
                ${p.managerId === 'PM_2' ? '<span style="color:var(--warning)">🔒 PM Assigned</span>' : ''}
            </div>
        </div>`;
    }).join('');
}

// Drill-down from portfolio into project's work hierarchy
window.drillToProject = (projectId, projectName) => {
    setBreadcrumb([
        { label: '🏠 Home', view: 'dashboard' },
        { label: `🗺️ Portfolio`, view: 'portfolio' },
        { label: `📁 ${projectName}`, view: 'tasks', id: projectId }
    ]);
    // Expand this project's items in the work hierarchy
    navTo('tasks');
    // After rendering, auto-expand this project
    setTimeout(() => {
        const container = document.getElementById(`${projectId}-children`);
        const icon = document.querySelector(`[onclick*="${projectId}-children"]`);
        if (container && !container.classList.contains('expanded')) {
            container.classList.add('expanded');
            if (icon) icon.classList.add('expanded');
        }
    }, 100);
};

// ─────────────────────────────────────────────
// WORK HIERARCHY
// ─────────────────────────────────────────────
function createItemNode(item, type, childrenMarkup = '', extra = {}) {
    const colorClass = getDeadlineColor(item.planned_end, item.status);
    const isLocked = false; // locking is now visual only via RBAC filter at the project level

    const addBtns = {
        Project:   `<button class="item-status-btn" style="border-color:rgba(16,212,122,.4)" onclick="openCreateModal('Milestone','${item.id}')">+ Milestone</button>`,
        Milestone: `<button class="item-status-btn" style="border-color:rgba(16,212,122,.4)" onclick="openCreateModal('Task','${item.id}')">+ Task</button>`,
        Task:      `<button class="item-status-btn" style="border-color:rgba(16,212,122,.4)" onclick="openCreateModal('Subtask','${item.id}')">+ Subtask</button>`
    };
    const addBtn = addBtns[type] || '';

    let toggleHtml = `<span style="width:20px;display:inline-block"></span>`;
    let childrenWrapper = '';
    if (childrenMarkup && childrenMarkup.trim()) {
        toggleHtml = `<span class="toggle-icon" onclick="toggleChildren(event,'${item.id}-children',this)">▶</span>`;
        childrenWrapper = `<div id="${item.id}-children" class="children-container">${childrenMarkup}</div>`;
    }

    const pBadge = item.priority ? priorityBadge(item.priority) : '';
    const pBar   = type === 'Task' ? progressBar(item.id) : '';
    const docFlag = item.requires_document ? (item.attachment_url ? ' 📄✅' : ' 📎') : '';
    const auditComments = db.audit_log.filter(a => a.itemId === item.id);
    const commentBtn = `<button class="item-status-btn" onclick="openCommentPanel('${item.id}','${type}','${item.name.replace(/'/g,"\\'")}')">💬${auditComments.length > 0 ? ` ${auditComments.length}` : ''}</button>`;
    const predMark = item.predecessor_id
        ? `<span style="font-size:9px;color:var(--warning);margin-left:2px" title="Has predecessor">⛓</span>`
        : '';

    return `
    <div class="work-item ${isLocked ? 'locked' : ''}">
        <div class="item-left" onclick="const t=this.querySelector('.toggle-icon');if(t&&t.innerHTML.trim()==='▶')t.click()">
            ${toggleHtml}
            <div class="status-indicator ${colorClass}"></div>
            <div class="item-type">${type}</div>
            <div style="display:flex;flex-direction:column;gap:3px;min-width:0">
                <div class="item-name">${item.name}${docFlag}${predMark}</div>
                ${pBar}
            </div>
            ${pBadge}
        </div>
        <div class="item-right">
            <div class="item-dates">
                <span style="font-weight:600;font-size:11px">${item.status}</span>
                <span>${item.planned_start || '—'} → ${item.planned_end || '—'}</span>
            </div>
            ${commentBtn}
            <button class="item-status-btn" onclick="openEditModal('${item.id}','${type}')">✏️</button>
            ${addBtn}
            <button class="item-status-btn" onclick="openStatusModal('${item.id}','${type}','${item.name.replace(/'/g,"\\'")}',${!!item.requires_document})">Change State</button>
            <button class="item-status-btn btn-del" onclick="confirmDelete('${item.id}','${type}','${item.name.replace(/'/g,"\\'")}')">🗑</button>
        </div>
    </div>
    ${childrenWrapper}`;
}

function renderWorkItems() {
    const container = document.getElementById('work-items-container');
    const vp = visibleProjects();
    container.innerHTML = '';
    if (!vp.length) {
        container.innerHTML = `<div class="empty-state">
            <div class="empty-state-icon">🗂️</div>
            <div class="empty-state-title">No Projects Visible</div>
            <div>Click <strong>+ New Project</strong> to create your first project.</div>
        </div>`;
        return;
    }
    let html = '';
    vp.forEach(p => {
        let mHtml = '';
        db.milestones.filter(m => m.projectId === p.id).forEach(m => {
            let tHtml = '';
            db.tasks.filter(t => t.milestoneId === m.id).forEach(t => {
                let sHtml = '';
                db.subtasks.filter(s => s.taskId === t.id).forEach(s => {
                    sHtml += `<div class="node-subtask">${createItemNode(s, 'Subtask', '', {})}</div>`;
                });
                tHtml += `<div class="node-task">${createItemNode(t, 'Task', sHtml, {})}</div>`;
            });
            mHtml += `<div class="node-milestone">${createItemNode(m, 'Milestone', tHtml, {})}</div>`;
        });
        html += `<div class="node-project">${createItemNode(p, 'Project', mHtml, {})}</div>`;
    });
    container.innerHTML = html;
}

window.toggleChildren = (event, containerId, iconEl) => {
    event.stopPropagation();
    const c = document.getElementById(containerId);
    if (!c) return;
    c.classList.toggle('expanded');
    iconEl.classList.toggle('expanded');
};

// ─────────────────────────────────────────────
// KANBAN BOARD
// ─────────────────────────────────────────────
function populateKanbanSelect() {
    const sel = document.getElementById('kanban-milestone-select');
    const prev = sel.value;
    sel.innerHTML = '<option value="">Select a Milestone…</option>';
    const vp = visibleProjects();
    const vpIds = new Set(vp.map(p => p.id));
    db.milestones
        .filter(m => vpIds.has(m.projectId))
        .forEach(m => {
            const p = db.projects.find(x => x.id === m.projectId);
            sel.innerHTML += `<option value="${m.id}" ${m.id === prev ? 'selected' : ''}>
                ${p ? p.name + ' › ' : ''}${m.name}
            </option>`;
        });
    if (prev) sel.value = prev;
}

function renderKanban() {
    const milestoneId = document.getElementById('kanban-milestone-select').value;
    const cols = { 'Yet to start':'kan-yet', 'Started':'kan-started', 'On hold':'kan-hold', 'Completed':'kan-done' };
    Object.values(cols).forEach(id => { document.getElementById(id).innerHTML = ''; });

    if (!milestoneId) {
        Object.values(cols).forEach(id => {
            document.getElementById(id).innerHTML = '<div class="kan-empty">Select a milestone above</div>';
        });
        return;
    }

    const tasks = db.tasks.filter(t => t.milestoneId === milestoneId);
    if (!tasks.length) {
        Object.values(cols).forEach(id => {
            document.getElementById(id).innerHTML = '<div class="kan-empty">No tasks yet</div>';
        });
        return;
    }

    tasks.forEach(t => {
        const colId = cols[t.status] || 'kan-yet';
        const subs  = db.subtasks.filter(s => s.taskId === t.id);
        const pct   = subs.length ? Math.round(subs.filter(s => s.status === 'Completed').length / subs.length * 100) : null;
        const col   = getDeadlineColor(t.planned_end, t.status);
        const dotC  = col === 'status-red' ? 'var(--danger)' : col === 'status-yellow' ? 'var(--warning)' : col === 'status-green' ? 'var(--success)' : '#2A3650';
        document.getElementById(colId).innerHTML += `
        <div class="kanban-card" draggable="true"
            ondragstart="kanDragStart(event,'${t.id}')"
            onclick="openStatusModal('${t.id}','Task','${t.name.replace(/'/g,"\\'")}',${!!t.requires_document})">
            <div style="display:flex;justify-content:space-between;align-items:flex-start;gap:8px">
                <h4>${t.name}${t.requires_document ? ' 📎' : ''}</h4>
                ${t.priority ? priorityBadge(t.priority) : ''}
            </div>
            ${pct !== null ? `<div class="progress-wrap" style="margin:7px 0">
                <div class="progress-bar"><div class="progress-fill" style="width:${pct}%;background:${pct===100?'var(--success)':'var(--accent-primary)'}"></div></div>
                <span class="progress-label">${pct}%</span>
            </div>` : ''}
            <div class="kanban-card-meta">
                <span style="display:flex;align-items:center;gap:4px">
                    <span style="width:6px;height:6px;border-radius:50%;background:${dotC};display:inline-block"></span>
                    ${t.status}
                </span>
                <span>${t.planned_end || 'No date'}</span>
            </div>
        </div>`;
    });

    Object.entries(cols).forEach(([status, id]) => {
        const col = document.getElementById(id);
        col.ondragover  = e => { e.preventDefault(); col.style.background = 'rgba(59,130,246,0.07)'; };
        col.ondragleave = () => { col.style.background = ''; };
        col.ondrop      = e => {
            e.preventDefault();
            col.style.background = '';
            const taskId = e.dataTransfer.getData('taskId');
            const task   = db.tasks.find(t => t.id === taskId);
            if (task && task.status !== status) {
                openStatusModal(taskId, 'Task', task.name, !!task.requires_document, status);
            }
        };
    });
}

window.kanDragStart = (e, taskId) => e.dataTransfer.setData('taskId', taskId);
document.getElementById('kanban-milestone-select').addEventListener('change', renderKanban);

// ─────────────────────────────────────────────
// GANTT CHART WITH CRITICAL PATH DETECTION
// ─────────────────────────────────────────────
function populateGanttSelect() {
    const sel  = document.getElementById('gantt-project-select');
    const prev = sel.value;
    sel.innerHTML = '<option value="">Select a Project…</option>';
    visibleProjects().forEach(p => {
        sel.innerHTML += `<option value="${p.id}" ${p.id === prev ? 'selected' : ''}>${p.name}</option>`;
    });
    if (prev) sel.value = prev;
}

const ganttExpanded = {};

// Critical path detection: find the chain of tasks with the longest total duration
function detectCriticalPath(tasks) {
    // Build adjacency: successor → predecessor
    // For each task compute Early Finish (EF) via forward pass
    const taskMap = {};
    tasks.forEach(t => taskMap[t.id] = { ...t, ef: 0, lf: 0 });

    // Topological sort
    const sorted = [];
    const visited = new Set();
    function visit(id) {
        if (visited.has(id)) return;
        visited.add(id);
        const t = taskMap[id];
        if (t && t.predecessor_id && taskMap[t.predecessor_id]) visit(t.predecessor_id);
        sorted.push(id);
    }
    tasks.forEach(t => visit(t.id));

    // Forward pass
    sorted.forEach(id => {
        const t = taskMap[id];
        if (!t) return;
        const dur = t.planned_start && t.planned_end
            ? dateDiffDays(t.planned_start, t.planned_end) : 0;
        const predEF = t.predecessor_id && taskMap[t.predecessor_id]
            ? taskMap[t.predecessor_id].ef : 0;
        t.ef = predEF + dur;
    });

    // Project EF
    const projectEF = Math.max(...Object.values(taskMap).map(t => t.ef), 0);

    // Backward pass
    for (let i = sorted.length - 1; i >= 0; i--) {
        const t = taskMap[sorted[i]];
        if (!t) continue;
        const dur = t.planned_start && t.planned_end ? dateDiffDays(t.planned_start, t.planned_end) : 0;
        // Find successors
        const successors = tasks.filter(s => s.predecessor_id === t.id).map(s => taskMap[s.id]);
        if (!successors.length) { t.lf = projectEF; }
        else { t.lf = Math.min(...successors.map(s => s.lf - (s.ef - (taskMap[s.predecessor_id]?.ef || 0)))); }
        t.float = t.lf - t.ef;
    }

    const cpIds = new Set(Object.values(taskMap).filter(t => t.float === 0).map(t => t.id));
    return cpIds;
}

function renderGantt() {
    const projectId = document.getElementById('gantt-project-select').value;
    const container = document.getElementById('gantt-container');
    const cpOnly    = document.getElementById('gantt-cp-only')?.checked;

    if (!projectId) {
        container.innerHTML = '<div class="empty-state"><div class="empty-state-icon">📅</div><div>Select a project above to view its Gantt chart.</div></div>';
        return;
    }

    // Build rows array
    const rows = [];
    const milestones = db.milestones.filter(m => m.projectId === projectId);
    milestones.forEach(m => {
        rows.push({ id:m.id, name:m.name, type:'Milestone', depth:0,
            planned_start:m.planned_start, planned_end:m.planned_end, status:m.status,
            predecessor_id:m.predecessor_id });
        const tasks = db.tasks.filter(t => t.milestoneId === m.id);
        tasks.forEach(t => {
            rows.push({ id:t.id, name:t.name, type:'Task', depth:1,
                planned_start:t.planned_start, planned_end:t.planned_end, status:t.status,
                priority:t.priority, predecessor_id:t.predecessor_id, parentId:m.id,
                requires_document:t.requires_document });
            const subs = db.subtasks.filter(s => s.taskId === t.id);
            subs.forEach(s => {
                rows.push({ id:s.id, name:s.name, type:'Subtask', depth:2,
                    planned_start:s.planned_start, planned_end:s.planned_end, status:s.status,
                    priority:s.priority, predecessor_id:s.predecessor_id, parentId:t.id });
            });
        });
    });

    if (!rows.length) {
        container.innerHTML = '<div class="empty-state">No milestones yet. Add milestones and tasks to see the Gantt chart.</div>';
        return;
    }

    // Detect critical path on tasks
    const allTasks = rows.filter(r => r.type === 'Task' || r.type === 'Subtask');
    const cpIds = detectCriticalPath(allTasks);

    // Date range
    const dated = rows.filter(r => r.planned_start && r.planned_end);
    if (!dated.length) {
        container.innerHTML = '<div class="empty-state">No items have planned dates yet.</div>';
        return;
    }
    const allDates = dated.flatMap(r => [new Date(r.planned_start), new Date(r.planned_end)]);
    let minDate = new Date(Math.min(...allDates));
    let maxDate = new Date(Math.max(...allDates));
    minDate.setDate(minDate.getDate() - 2);
    maxDate.setDate(maxDate.getDate() + 3);
    const totalDays = Math.ceil((maxDate - minDate) / 86400000);
    const DAY_PX    = Math.max(16, Math.min(34, Math.floor(900 / totalDays)));
    const timelineW = totalDays * DAY_PX;
    const ROW_H     = 36;

    function dateToPx(s) {
        return Math.round(((new Date(s) - minDate) / 86400000) * DAY_PX);
    }

    // Expand state defaults
    rows.forEach(r => {
        if (r.type === 'Milestone') ganttExpanded[r.id] = ganttExpanded[r.id] !== false;
    });

    function isVisible(row) {
        if (row.type === 'Milestone') return true;
        if (row.type === 'Task')    return !!ganttExpanded[row.parentId];
        if (row.type === 'Subtask') return !!ganttExpanded[row.parentId];
        return false;
    }

    let visibleRows = rows.filter(isVisible);
    if (cpOnly) visibleRows = visibleRows.filter(r => r.type === 'Milestone' || cpIds.has(r.id));

    // Date header ticks
    const step = totalDays < 14 ? 1 : totalDays < 30 ? 3 : totalDays < 90 ? 7 : 14;
    let dateTicks = '';
    for (let d = 0; d <= totalDays; d += step) {
        const dt = new Date(minDate);
        dt.setDate(dt.getDate() + d);
        const lbl = dt.toLocaleDateString('en-GB', { day:'2-digit', month:'short' });
        dateTicks += `<div style="position:absolute;left:${d*DAY_PX}px;font-size:9px;color:var(--text-secondary);white-space:nowrap;transform:translateX(-50%)">${lbl}</div>`;
    }

    const todayPx = dateToPx(today());
    let nameRowsHtml = '';
    let barRowsHtml  = '';
    const barPositions = {};

    visibleRows.forEach((row, idx) => {
        const y  = idx * ROW_H;
        const cy = y + ROW_H / 2;
        const indentPx = row.depth * 20 + 8;
        const isCp = cpIds.has(row.id);

        const barCls    = getGanttBarClass(row);
        const barColour = barCls === 'gantt-bar-completed' ? 'var(--success)'
            : barCls === 'gantt-bar-started'  ? 'var(--accent-primary)'
            : barCls === 'gantt-bar-hold'     ? 'var(--warning)'
            : barCls === 'gantt-bar-overdue'  ? 'var(--danger)'
            : 'rgba(107,127,163,.55)';

        const hasChildren = row.type === 'Milestone'
            ? rows.some(r => r.type === 'Task' && r.parentId === row.id)
            : row.type === 'Task'
                ? rows.some(r => r.type === 'Subtask' && r.parentId === row.id)
                : false;
        const isExpanded = !!ganttExpanded[row.id];
        const toggleIcon = hasChildren
            ? `<span onclick="ganttToggle('${row.id}')" style="cursor:pointer;display:inline-flex;align-items:center;justify-content:center;width:14px;height:14px;border-radius:3px;background:rgba(255,255,255,.07);font-size:8px;margin-right:4px;transform:rotate(${isExpanded?90:0}deg);transition:transform .2s">▶</span>`
            : `<span style="display:inline-block;width:18px"></span>`;

        const typeStyle = row.type === 'Milestone' ? 'font-weight:700;color:var(--warning)'
            : row.type === 'Task' ? 'font-weight:600;color:var(--text-primary)'
            : 'color:var(--text-secondary)';

        const cpGlow   = isCp ? 'background:rgba(239,68,68,0.06);' : '';
        const rowBg    = idx % 2 === 0 ? 'rgba(255,255,255,.012)' : 'rgba(0,0,0,.08)';
        const cpBorder = isCp ? 'border-left:2px solid var(--danger);' : '';

        nameRowsHtml += `
        <div style="display:flex;align-items:center;height:${ROW_H}px;padding-left:${indentPx}px;padding-right:8px;background:${rowBg};${cpGlow}${cpBorder}border-bottom:1px solid rgba(255,255,255,.025);box-sizing:border-box;overflow:hidden">
            ${toggleIcon}
            <span style="font-size:11px;${typeStyle};white-space:nowrap;overflow:hidden;text-overflow:ellipsis;flex:1" title="${row.name}">${row.name}</span>
            ${isCp && (row.type==='Task'||row.type==='Subtask') ? '<span style="font-size:8px;color:var(--danger);margin-left:4px;flex-shrink:0">CP</span>' : ''}
            ${row.predecessor_id ? '<span style="font-size:8px;color:var(--warning);margin-left:3px;flex-shrink:0">⛓</span>' : ''}
            <span style="font-size:8px;color:var(--text-muted);flex-shrink:0;margin-left:5px">${row.status.slice(0,3)}</span>
        </div>`;

        let barHtml = '';
        if (row.planned_start && row.planned_end) {
            const x = dateToPx(row.planned_start);
            const w = Math.max(DAY_PX * 0.5, dateToPx(row.planned_end) - x);
            barPositions[row.id] = { cx: x + w, cy };
            const cpOutline = isCp && row.type !== 'Milestone' ? `;box-shadow:0 0 0 1.5px var(--danger)` : '';
            barHtml = `<div title="${row.name} | ${row.planned_start} → ${row.planned_end} | ${row.status}"
                style="position:absolute;left:${x}px;width:${w}px;top:${row.type==='Milestone'?6:8}px;height:${row.type==='Milestone'?ROW_H-12:ROW_H-16}px;background:${barColour};border-radius:${row.type==='Subtask'?3:4}px;opacity:.85;display:flex;align-items:center;padding:0 5px;font-size:9px;color:#fff;white-space:nowrap;overflow:hidden${cpOutline}">
                ${w > 40 ? row.name.slice(0, 22) : ''}
            </div>`;
        } else {
            barPositions[row.id] = null;
        }

        barRowsHtml += `<div style="position:relative;height:${ROW_H}px;background:${rowBg};border-bottom:1px solid rgba(255,255,255,.025)">${barHtml}</div>`;
    });

    // Dependency arrows (SVG)
    let depArrows = '';
    visibleRows.forEach(row => {
        if (!row.predecessor_id) return;
        const from = barPositions[row.predecessor_id];
        const to   = barPositions[row.id];
        if (!from || !to) return;
        const tx = row.planned_start ? dateToPx(row.planned_start) : null;
        if (tx === null) return;
        const mx = from.cx + 8;
        const isCp = cpIds.has(row.id) && cpIds.has(row.predecessor_id);
        const col  = isCp ? 'rgba(239,68,68,.7)' : 'rgba(245,158,11,.55)';
        depArrows += `<path d="M${from.cx},${from.cy} L${mx},${from.cy} L${mx},${to.cy} L${tx},${to.cy}" fill="none" stroke="${col}" stroke-width="1.5" stroke-dasharray="4,3" marker-end="url(#arr${isCp?'cp':''})"/>`;
    });

    const totalH = visibleRows.length * ROW_H;
    const svgOverlay = depArrows ? `
    <svg style="position:absolute;top:0;left:0;width:${timelineW}px;height:${totalH}px;pointer-events:none;overflow:visible" xmlns="http://www.w3.org/2000/svg">
        <defs>
            <marker id="arr" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                <path d="M0,0 L6,3 L0,6 Z" fill="rgba(245,158,11,.8)"/>
            </marker>
            <marker id="arrcp" markerWidth="6" markerHeight="6" refX="3" refY="3" orient="auto">
                <path d="M0,0 L6,3 L0,6 Z" fill="rgba(239,68,68,.9)"/>
            </marker>
        </defs>
        ${depArrows}
    </svg>` : '';

    // Grid lines
    const gridLines = Array.from({length: Math.ceil(totalDays/step)}, (_, i) => {
        const px = (i * step) * DAY_PX;
        return `<div style="position:absolute;left:${px}px;top:0;bottom:0;width:1px;background:rgba(255,255,255,.03)"></div>`;
    }).join('');

    container.innerHTML = `
    <div style="display:flex;overflow:hidden;border:1px solid var(--glass-border);border-radius:10px">
        <div style="width:260px;flex-shrink:0;border-right:1px solid var(--glass-border)">
            <div style="height:36px;display:flex;align-items:center;padding:0 12px;background:rgba(0,0,0,.3);border-bottom:1px solid var(--glass-border)">
                <span style="font-size:10px;font-weight:700;color:var(--text-secondary);text-transform:uppercase;letter-spacing:.5px">Work Item</span>
            </div>
            ${nameRowsHtml}
        </div>
        <div style="flex:1;overflow-x:auto;overflow-y:hidden" id="gantt-scroll-area">
            <div style="height:36px;position:relative;width:${timelineW}px;background:rgba(0,0,0,.3);border-bottom:1px solid var(--glass-border)">
                ${dateTicks}
                <div style="position:absolute;left:${todayPx}px;top:0;bottom:0;width:1px;background:var(--danger);opacity:.7"></div>
            </div>
            <div style="position:relative;width:${timelineW}px">
                <div style="position:absolute;left:${todayPx}px;top:0;bottom:0;width:1px;background:var(--danger);opacity:.3;z-index:1"></div>
                ${gridLines}
                ${barRowsHtml}
                ${svgOverlay}
            </div>
        </div>
    </div>

    <div style="display:flex;gap:14px;margin-top:12px;flex-wrap:wrap;font-size:11px;color:var(--text-secondary)">
        <span><span style="display:inline-block;width:9px;height:9px;border-radius:2px;background:rgba(107,127,163,.55);margin-right:3px"></span>Yet to start</span>
        <span><span style="display:inline-block;width:9px;height:9px;border-radius:2px;background:var(--accent-primary);margin-right:3px"></span>Started</span>
        <span><span style="display:inline-block;width:9px;height:9px;border-radius:2px;background:var(--warning);margin-right:3px;opacity:.7"></span>On Hold</span>
        <span><span style="display:inline-block;width:9px;height:9px;border-radius:2px;background:var(--success);margin-right:3px"></span>Completed</span>
        <span><span style="display:inline-block;width:9px;height:9px;border-radius:2px;background:var(--danger);margin-right:3px"></span>Overdue</span>
        <span style="margin-left:6px"><span style="color:var(--danger);font-weight:700">CP</span> = Critical Path &nbsp;|&nbsp; <span style="color:rgba(245,158,11,.8)">- - →</span> dependency</span>
        <span>🔴 = Today</span>
    </div>`;
}

window.ganttToggle = (id) => { ganttExpanded[id] = !ganttExpanded[id]; renderGantt(); };
document.getElementById('gantt-project-select').addEventListener('change', renderGantt);

// ─────────────────────────────────────────────
// MILESTONE TRACKER
// ─────────────────────────────────────────────
const STAGE_COLOURS = [
    {bg:'#16A34A',text:'#fff'},{bg:'#2D9B6F',text:'#fff'},{bg:'#2563EB',text:'#fff'},
    {bg:'#1E3A5F',text:'#fff'},{bg:'#6B21A8',text:'#fff'},{bg:'#BE185D',text:'#fff'}
];

function populateMilestoneTrackerSelect() {
    const sel  = document.getElementById('milestonetrack-project-select');
    const prev = sel.value;
    sel.innerHTML = '<option value="__ALL__">📂 All Projects</option>';
    visibleProjects().forEach(p => {
        sel.innerHTML += `<option value="${p.id}" ${p.id === prev ? 'selected' : ''}>${p.name}</option>`;
    });
    if (prev && prev !== '__ALL__') sel.value = prev;
}

function buildTrackerForProject(projectId) {
    const project    = db.projects.find(p => p.id === projectId);
    if (!project) return '';
    const milestones = db.milestones.filter(m => m.projectId === projectId);
    if (!milestones.length) {
        return `<div style="color:var(--text-secondary);font-size:13px;padding:16px 0;">No milestones yet for <strong>${project.name}</strong>.</div>`;
    }

    const nodes = [];
    milestones.forEach((m, mi) => {
        const tasks = db.tasks.filter(t => t.milestoneId === m.id);
        const pre  = tasks.slice(0, Math.ceil(tasks.length / 2));
        const post = tasks.slice(Math.ceil(tasks.length / 2));
        pre.forEach(t  => nodes.push({ kind:'task', item:t, stageIdx:mi }));
        nodes.push({ kind:'milestone', item:m, stageIdx:mi });
        post.forEach(t => nodes.push({ kind:'task', item:t, stageIdx:mi }));
    });

    const colWidth   = Math.max(90, Math.floor(900 / nodes.length));
    const totalW     = colWidth * nodes.length + 80;
    const stageWidths = milestones.map((m, mi) => nodes.filter(n => n.stageIdx === mi).length);

    let aboveHtml = '', nodesHtml = '', belowHtml = '';

    nodes.forEach(n => {
        const { kind, item, stageIdx } = n;
        const done = item.status === 'Completed';
        if (kind === 'milestone') {
            aboveHtml += `
            <div class="mtrack-col" style="width:${colWidth}px;flex-shrink:0">
                <div class="mtrack-label-up">
                    <div class="ml-name ${done ? 'completed' : ''}">${item.name}</div>
                    <div class="ml-desc">${item.status}${item.planned_end ? '<br/>' + item.planned_end : ''}</div>
                </div>
                <div class="mtrack-dot-up ${done ? 'completed' : ''}" style="height:40px"></div>
            </div>`;
            nodesHtml += `<div style="width:${colWidth}px;flex-shrink:0;display:flex;justify-content:center">
                <div class="mtrack-node milestone-node ${done ? 'completed-node' : ''}" title="${item.name} — ${item.status}"></div>
            </div>`;
            belowHtml += `<div class="mtrack-col" style="width:${colWidth}px;flex-shrink:0"><div style="height:40px"></div></div>`;
        } else {
            aboveHtml += `<div class="mtrack-col" style="width:${colWidth}px;flex-shrink:0"><div style="height:86px"></div></div>`;
            nodesHtml += `<div style="width:${colWidth}px;flex-shrink:0;display:flex;justify-content:center">
                <div class="mtrack-node ${done ? 'completed-node' : ''}" title="${item.name} — ${item.status}"></div>
            </div>`;
            belowHtml += `
            <div class="mtrack-col" style="width:${colWidth}px;flex-shrink:0">
                <div class="mtrack-dot-down" style="height:40px"></div>
                <div class="mtrack-label-down">
                    <div class="t-name">${item.name}</div>
                    <div class="t-date">${item.planned_start || ''} ${item.planned_end ? '→ ' + item.planned_end : ''}</div>
                    <div style="margin-top:3px">${priorityBadge(item.priority)}</div>
                </div>
            </div>`;
        }
    });

    const stagesHtml = milestones.map((m, mi) => {
        const col = STAGE_COLOURS[mi % STAGE_COLOURS.length];
        return `<div class="mtrack-stage" style="background:${col.bg};color:${col.text};flex:${stageWidths[mi]}">
            <span style="font-size:9px;opacity:.7;margin-right:4px">Stage ${mi+1}</span>
            <strong style="font-size:11px">${m.name}</strong>
        </div>`;
    }).join('');

    return `
    <div class="mtrack-wrapper">
        <div class="mtrack-scene" style="width:${totalW}px">
            <div class="mtrack-above" style="width:${totalW-74}px">
                <div style="display:flex;width:100%">${aboveHtml}</div>
            </div>
            <div style="position:absolute;top:50%;left:0;right:0;transform:translateY(-50%)">
                <div class="mtrack-spine" style="margin:0 40px"></div>
                <div style="position:absolute;top:50%;left:40px;right:74px;transform:translateY(-50%);display:flex;align-items:center">
                    ${nodesHtml}
                </div>
            </div>
            <div class="mtrack-below" style="width:${totalW-74}px">
                <div style="display:flex;width:100%">${belowHtml}</div>
            </div>
        </div>
        <div class="mtrack-stages" style="width:${totalW-80}px;margin-top:16px">${stagesHtml}</div>
    </div>`;
}

function renderMilestoneTracker() {
    const container = document.getElementById('milestonetrack-container');
    const projectId = document.getElementById('milestonetrack-project-select').value;

    if (!projectId || projectId === '__ALL__') {
        const vp = visibleProjects();
        if (!vp.length) {
            container.innerHTML = '<div class="empty-state"><div class="empty-state-icon">🏁</div><div>No projects yet.</div></div>';
            return;
        }
        container.innerHTML = vp.map(p => `
            <div style="margin-bottom:44px">
                <div style="display:flex;align-items:center;gap:10px;margin-bottom:4px;padding:0 8px">
                    <div style="width:8px;height:8px;border-radius:50%;background:${p.status==='Completed'?'var(--success)':p.status==='Started'?'var(--accent-primary)':'#2A3650'}"></div>
                    <h4 style="font-size:15px;font-weight:700">${p.name}</h4>
                    ${statusPill(p.status)}
                </div>
                <div style="height:1px;background:var(--glass-border);margin:8px 0 4px"></div>
                ${buildTrackerForProject(p.id)}
            </div>`).join('');
        return;
    }
    const milestones = db.milestones.filter(m => m.projectId === projectId);
    if (!milestones.length) {
        container.innerHTML = '<div class="empty-state">No milestones in this project yet.</div>';
        return;
    }
    container.innerHTML = buildTrackerForProject(projectId);
}

document.getElementById('milestonetrack-project-select').addEventListener('change', renderMilestoneTracker);

// ─────────────────────────────────────────────
// AUDIT LOG VIEW
// ─────────────────────────────────────────────
window.renderAuditLog = function() {
    const container = document.getElementById('audit-log-list');
    if (!container) return;
    const typeFilter   = document.getElementById('audit-filter-type')?.value || '';
    const statusFilter = document.getElementById('audit-filter-status')?.value || '';

    let entries = [...db.audit_log];
    if (typeFilter)   entries = entries.filter(a => a.type === typeFilter);
    if (statusFilter) entries = entries.filter(a => a.newStatus === statusFilter);

    if (!entries.length) {
        container.innerHTML = `<div class="empty-state">
            <div class="empty-state-icon">📋</div>
            <div class="empty-state-title">No Audit Entries</div>
            <div>State transitions will appear here with their mandatory comments.</div>
        </div>`;
        return;
    }

    const iconMap = { 'Started':'audit-icon-started', 'Completed':'audit-icon-completed', 'On hold':'audit-icon-hold', 'Yet to start':'audit-icon-yet' };
    const emojiMap = { 'Started':'🔵', 'Completed':'✅', 'On hold':'⏸️', 'Yet to start':'⭕' };
    const toClass  = { 'Started':'audit-to-started', 'Completed':'audit-to-completed', 'On hold':'audit-to-hold', 'Yet to start':'audit-to-yet' };

    container.innerHTML = entries.map(a => `
    <div class="audit-entry">
        <div class="audit-icon ${iconMap[a.newStatus] || 'audit-icon-yet'}">${emojiMap[a.newStatus] || '⭕'}</div>
        <div class="audit-body">
            <div class="audit-title">
                <strong>${a.itemName || '—'}</strong>
                <span style="font-size:10px;color:var(--text-secondary);font-weight:400"> — ${a.type || '?'}</span>
            </div>
            <div class="audit-meta">
                <div class="audit-transition">
                    <span class="audit-from">${a.oldStatus || '—'}</span>
                    <span style="color:var(--text-muted)">→</span>
                    <span class="${toClass[a.newStatus] || 'audit-to-yet'}">${a.newStatus}</span>
                </div>
                <span>👤 ${a.role || 'System'}</span>
                <span>🕐 ${new Date(a.timestamp).toLocaleString()}</span>
            </div>
            ${a.comment ? `<div class="audit-comment">"${a.comment}"</div>` : ''}
        </div>
    </div>`).join('');
};

// ─────────────────────────────────────────────
// COMMENT / AUDIT THREAD PANEL
// ─────────────────────────────────────────────
window.openCommentPanel = (itemId, type, name) => {
    document.getElementById('comment-panel-subtitle').innerText = `${type}: ${name}`;
    const list     = document.getElementById('comment-thread-list');
    const comments = db.audit_log.filter(a => a.itemId === itemId);
    const toClass  = { 'Started':'audit-to-started', 'Completed':'audit-to-completed', 'On hold':'audit-to-hold', 'Yet to start':'audit-to-yet' };

    list.innerHTML = !comments.length
        ? '<span style="color:var(--text-secondary);font-size:13px">No state transitions logged for this item yet.</span>'
        : comments.map(c => `
            <div class="comment-bubble">
                <div class="comment-meta">
                    <span>👤 ${c.role || 'System'}</span>
                    <span>·</span>
                    <span>${new Date(c.timestamp).toLocaleString()}</span>
                    <span>·</span>
                    <span class="comment-status-chip ${toClass[c.newStatus] || ''}">${c.newStatus}</span>
                </div>
                <div class="comment-text">${c.comment}</div>
            </div>`).join('');
    document.getElementById('comment-panel').classList.remove('hidden');
};

document.getElementById('btn-close-comments').addEventListener('click', () => {
    document.getElementById('comment-panel').classList.add('hidden');
});

// ─────────────────────────────────────────────
// NAVIGATION
// ─────────────────────────────────────────────
document.querySelectorAll('.nav-item').forEach(btn => {
    btn.addEventListener('click', () => {
        const target = btn.getAttribute('data-target');
        navTo(target);
        // Reset breadcrumb on top-level nav clicks
        const labelMap = {
            dashboard:      '🏠 Home',
            portfolio:      '🗺️ Portfolio Map',
            tasks:          '🗂️ Work Hierarchy',
            kanban:         '📋 Kanban Board',
            gantt:          '📅 Gantt / CPM',
            milestonetrack: '🏁 Milestone Tracker',
            audit:          '📋 Audit Log',
            templates:      '📄 Templates'
        };
        setBreadcrumb([
            { label: '🏠 Home', view: 'dashboard' },
            ...(target !== 'dashboard' ? [{ label: labelMap[target] || target, view: target }] : [])
        ]);
        if (target === 'kanban')         renderKanban();
        if (target === 'gantt')          renderGantt();
        if (target === 'milestonetrack') renderMilestoneTracker();
        if (target === 'audit')          renderAuditLog();
    });
});

document.getElementById('role-select').addEventListener('change', e => {
    activeRole = e.target.value;
    document.getElementById('role-description').innerText =
        activeRole === 'PORTFOLIO_MANAGER' ? '🌐 Global Access' : '🔒 Assigned Projects Only';
    renderApp();
});

// ─────────────────────────────────────────────
// STATUS CHANGE MODAL (Waterfall Gate)
// ─────────────────────────────────────────────
const modal         = document.getElementById('status-modal');
const statusForm    = document.getElementById('status-form');
const documentGroup = document.getElementById('document-upload-group');

window.openStatusModal = (id, type, name, reqDoc, presetStatus = null) => {
    let item = null;
    if (type === 'Project')   item = db.projects.find(x => x.id === id);
    if (type === 'Milestone') item = db.milestones.find(x => x.id === id);
    if (type === 'Task')      item = db.tasks.find(x => x.id === id);
    if (type === 'Subtask')   item = db.subtasks.find(x => x.id === id);

    // ── Dependency lock ─────────────────────────────
    if (item?.predecessor_id) {
        const pred = db.milestones.find(m => m.id === item.predecessor_id)
                  || db.tasks.find(t => t.id === item.predecessor_id)
                  || db.subtasks.find(s => s.id === item.predecessor_id);
        if (pred && pred.status !== 'Completed') {
            showToast(`🔒 Blocked! "${pred.name}" must be Completed first.`, 'error');
            return;
        }
    }

    document.getElementById('modal-item-name').innerText = `${type}: ${name}`;
    document.getElementById('modal-item-id').value   = id;
    document.getElementById('modal-item-type').value = type;
    document.getElementById('modal-comment').value   = '';
    document.getElementById('modal-document').value  = '';

    const statusSel = document.getElementById('modal-new-status');
    statusSel.value = presetStatus || (item ? item.status : 'Yet to start');

    if (type === 'Task' && reqDoc) {
        documentGroup.classList.remove('hidden');
        document.getElementById('modal-document').setAttribute('required', 'true');
    } else {
        documentGroup.classList.add('hidden');
        document.getElementById('modal-document').removeAttribute('required');
    }
    modal.classList.remove('hidden');
};

document.getElementById('btn-cancel-modal').addEventListener('click', () => modal.classList.add('hidden'));

statusForm.addEventListener('submit', e => {
    e.preventDefault();
    const id        = document.getElementById('modal-item-id').value;
    const type      = document.getElementById('modal-item-type').value;
    const newStatus = document.getElementById('modal-new-status').value;
    const comment   = document.getElementById('modal-comment').value.trim();

    if (!comment) { showToast('A mandatory comment is required!', 'error'); return; }
    if (comment.length < 5) { showToast('Comment too short — be descriptive.', 'error'); return; }

    // Document required check
    if (type === 'Task' && newStatus === 'Completed' && !documentGroup.classList.contains('hidden')) {
        const fileInput = document.getElementById('modal-document');
        if (!fileInput.files.length) {
            showToast('⚠️ Stage-Gate: Document upload required to complete this task!', 'error');
            return;
        }
        const task = db.tasks.find(t => t.id === id);
        if (task) task.attachment_url = fileInput.files[0].name;
    }

    updateItemStatus(id, type, newStatus, comment);
    saveDb();
    modal.classList.add('hidden');
    renderApp();
    showToast(`Status updated → ${newStatus}`);
});

// ─────────────────────────────────────────────
// CREATE / EDIT ENTITY MODAL
// ─────────────────────────────────────────────
const createModal = document.getElementById('create-modal');
const createForm  = document.getElementById('create-form');

window.openCreateModal = (type, parentId = null) => {
    document.getElementById('create-modal-title').innerText   = `Create New ${type}`;
    document.getElementById('create-modal-subtitle').innerText = `Provide details for the new ${type.toLowerCase()}`;
    document.getElementById('btn-create-submit').innerText    = 'Create';
    document.getElementById('create-type').value      = type;
    document.getElementById('create-parent-id').value = parentId || '';
    document.getElementById('create-name').value       = '';
    document.getElementById('create-desc').value       = '';
    document.getElementById('create-start-date').value = '';
    document.getElementById('create-end-date').value   = '';
    document.getElementById('pred-constraint-hint').innerText = '';
    document.getElementById('create-date-hint').innerText     = '';
    document.getElementById('create-predecessor').innerHTML   = '<option value="">None — independent start node</option>';

    const isProject  = type === 'Project';
    const isTask     = type === 'Task';
    const isSubtask  = type === 'Subtask';
    const isMilestone = type === 'Milestone';

    document.getElementById('create-manager-group').style.display    = isProject   ? 'block' : 'none';
    document.getElementById('create-dates-group').style.display      = (!isProject) ? 'block' : 'none';
    document.getElementById('create-document-group').style.display   = isTask      ? 'block' : 'none';
    document.getElementById('create-priority-group').style.display   = (isTask || isSubtask) ? 'block' : 'none';
    document.getElementById('create-predecessor-group').style.display= (!isProject) ? 'block' : 'none';

    // Template selector
    const tmplGroup = document.getElementById('create-template-group');
    if (isProject) {
        tmplGroup.style.display = 'block';
        populateTemplateSelect();
        document.getElementById('create-template-preview').innerText = '';
    } else {
        tmplGroup.style.display = 'none';
    }

    // Parent temporal hint
    if (!isProject && parentId) {
        let parent = null;
        if (isMilestone)  parent = db.projects.find(p => p.id === parentId);
        else if (isTask)  parent = db.milestones.find(m => m.id === parentId);
        else if (isSubtask) parent = db.tasks.find(t => t.id === parentId);
        if (parent?.planned_start && parent?.planned_end) {
            document.getElementById('create-date-hint').innerText =
                `📐 Parent envelope: ${parent.planned_start} → ${parent.planned_end}`;
            document.getElementById('create-start-date').min = parent.planned_start;
            document.getElementById('create-end-date').max   = parent.planned_end;
        }
    }

    // Populate predecessor dropdown (siblings only)
    const predSel = document.getElementById('create-predecessor');
    if (isMilestone && parentId) {
        db.milestones.filter(m => m.projectId === parentId)
            .forEach(m => predSel.innerHTML += `<option value="${m.id}">${m.name}</option>`);
    } else if (isTask && parentId) {
        db.tasks.filter(t => t.milestoneId === parentId)
            .forEach(t => predSel.innerHTML += `<option value="${t.id}">${t.name}</option>`);
    } else if (isSubtask && parentId) {
        db.subtasks.filter(s => s.taskId === parentId)
            .forEach(s => predSel.innerHTML += `<option value="${s.id}">${s.name}</option>`);
    }

    // When predecessor is picked, auto-constrain start date
    predSel.onchange = () => {
        const predId = predSel.value;
        if (!predId) { document.getElementById('pred-constraint-hint').innerText = ''; return; }
        let pred = db.milestones.find(x => x.id === predId)
                || db.tasks.find(x => x.id === predId)
                || db.subtasks.find(x => x.id === predId);
        if (pred?.planned_end) {
            document.getElementById('create-start-date').min   = pred.planned_end;
            document.getElementById('create-start-date').value = pred.planned_end;
            document.getElementById('pred-constraint-hint').innerText =
                `⛓ FS dependency: start locked to ≥ ${pred.planned_end} (predecessor end)`;
        }
    };

    delete createModal.dataset.editId;
    delete createModal.dataset.editType;
    createModal.classList.remove('hidden');
};

document.getElementById('btn-cancel-create').addEventListener('click', () => createModal.classList.add('hidden'));

// Edit existing item
window.openEditModal = (id, type) => {
    const collMap = { Project:db.projects, Milestone:db.milestones, Task:db.tasks, Subtask:db.subtasks };
    const item = collMap[type]?.find(i => i.id === id);
    if (!item) return;
    const parentId = item.projectId || item.milestoneId || item.taskId || null;
    openCreateModal(type, parentId);
    document.getElementById('create-modal-title').innerText  = `Edit ${type}`;
    document.getElementById('btn-create-submit').innerText   = 'Save Changes';
    document.getElementById('create-name').value             = item.name || '';
    document.getElementById('create-desc').value             = item.description || '';
    document.getElementById('create-start-date').value       = item.planned_start || '';
    document.getElementById('create-end-date').value         = item.planned_end || '';
    if (item.priority) document.getElementById('create-priority').value     = item.priority;
    if (item.predecessor_id) document.getElementById('create-predecessor').value = item.predecessor_id;
    const rdEl = document.getElementById('create-requires-doc');
    if (rdEl) rdEl.value = item.requires_document ? 'yes' : 'no';
    const mgrEl = document.getElementById('create-manager');
    if (mgrEl && item.managerId) mgrEl.value = item.managerId;
    // Remove self from predecessor dropdown
    const selfOpt = document.getElementById('create-predecessor').querySelector(`option[value="${id}"]`);
    if (selfOpt) selfOpt.remove();
    createModal.dataset.editId   = id;
    createModal.dataset.editType = type;
};

createForm.addEventListener('submit', e => {
    e.preventDefault();
    const type        = document.getElementById('create-type').value;
    const parentId    = document.getElementById('create-parent-id').value;
    const name        = document.getElementById('create-name').value.trim();
    const desc        = document.getElementById('create-desc').value;
    const startDate   = document.getElementById('create-start-date').value;
    const endDate     = document.getElementById('create-end-date').value;
    const predecessorId = document.getElementById('create-predecessor').value || null;
    const managerId   = document.getElementById('create-manager').value;
    const priority    = document.getElementById('create-priority').value;
    const requiresDoc = document.getElementById('create-requires-doc').value === 'yes';

    if (!name) { showToast('Name is required', 'error'); return; }

    if (type !== 'Project') {
        // Basic date sanity
        if (startDate && endDate && new Date(endDate) < new Date(startDate)) {
            showToast('End date cannot be before start date!', 'error'); return;
        }
        // Temporal envelope validation
        const envErr = validateTemporalEnvelope(type, parentId, startDate, endDate);
        if (envErr) { showToast(envErr, 'error'); return; }
    }

    // ── EDIT MODE ────────────────────────────────────────────────────────
    const editId = createModal.dataset.editId;
    if (editId) {
        const collMap = { Project:db.projects, Milestone:db.milestones, Task:db.tasks, Subtask:db.subtasks };
        const item = collMap[type]?.find(i => i.id === editId);
        if (item) {
            // Circular dependency check
            const coll = type === 'Milestone' ? db.milestones
                       : type === 'Task'      ? db.tasks
                       : type === 'Subtask'   ? db.subtasks : [];
            if (predecessorId && wouldCreateCycle(coll, editId, predecessorId)) {
                showToast('⚠️ Circular dependency detected! This would create a scheduling loop.', 'error');
                return;
            }
            item.name = name;
            item.description = desc;
            if (startDate) item.planned_start = startDate;
            if (endDate)   item.planned_end   = endDate;
            item.predecessor_id = predecessorId;
            if (priority)  item.priority = priority;
            if (type === 'Project' && managerId) item.managerId = managerId;
            if (type === 'Task') item.requires_document = requiresDoc;
        }
        delete createModal.dataset.editId;
        delete createModal.dataset.editType;
        saveDb();
        createModal.classList.add('hidden');
        renderApp();
        showToast(`${type} "${name}" updated!`);
        return;
    }

    // ── CREATE MODE ──────────────────────────────────────────────────────
    const newId = genId(type[0].toLowerCase());

    // Circular dependency check for new items
    if (predecessorId) {
        const coll = type === 'Milestone' ? db.milestones
                   : type === 'Task'      ? db.tasks
                   : type === 'Subtask'   ? db.subtasks : [];
        if (wouldCreateCycle(coll, newId, predecessorId)) {
            showToast('⚠️ Circular dependency detected!', 'error');
            return;
        }
    }

    if (type === 'Project') {
        db.projects.push({ id:newId, name, description:desc, status:'Yet to start', managerId });
        const templateId = document.getElementById('create-template-select')?.value;
        if (templateId) instantiateTemplate(templateId, newId);
    } else if (type === 'Milestone') {
        db.milestones.push({ id:newId, projectId:parentId, name, description:desc, status:'Yet to start',
            planned_start:startDate, planned_end:endDate, actual_start:null, actual_end:null,
            predecessor_id:predecessorId });
    } else if (type === 'Task') {
        db.tasks.push({ id:newId, milestoneId:parentId, name, description:desc, status:'Yet to start',
            priority, planned_start:startDate, planned_end:endDate, actual_start:null, actual_end:null,
            predecessor_id:predecessorId, requires_document:requiresDoc, attachment_url:null });
    } else if (type === 'Subtask') {
        db.subtasks.push({ id:newId, taskId:parentId, name, description:desc, status:'Yet to start',
            priority, planned_start:startDate, planned_end:endDate, actual_start:null, actual_end:null,
            predecessor_id:predecessorId });
    }

    saveDb();
    createModal.classList.add('hidden');
    renderApp();
    showToast(`${type} "${name}" created!`);
});

// ─────────────────────────────────────────────
// TEMPLATE SYSTEM
// ─────────────────────────────────────────────
let _tmplEditId  = null;
let _tmplMiIdx = 0, _tmplTiIdx = 0, _tmplSiIdx = 0;

function renderTemplates() {
    const container = document.getElementById('templates-container');
    if (!container) return;
    if (!db.templates.length) {
        container.innerHTML = `<div class="empty-state">
            <div class="empty-state-icon">📄</div>
            <div class="empty-state-title">No Templates Yet</div>
            <div>Templates let you scaffold repetitive project structures instantly.</div>
        </div>`;
        return;
    }
    container.innerHTML = db.templates.map(t => {
        const mC = t.milestones.length;
        const tC = t.milestones.reduce((a,m) => a + m.tasks.length, 0);
        const sC = t.milestones.reduce((a,m) => a + m.tasks.reduce((b,tk) => b + (tk.subtasks||[]).length, 0), 0);
        return `<div class="template-card">
            <div class="template-card-header">
                <div style="flex:1">
                    <div class="template-card-name">📄 ${t.name}</div>
                    <div class="template-card-desc">${t.description || '—'}</div>
                    <div class="template-card-stats">
                        <span>🏁 ${mC} Milestone${mC!==1?'s':''}</span>
                        <span>📋 ${tC} Task${tC!==1?'s':''}</span>
                        <span>🔹 ${sC} Subtask${sC!==1?'s':''}</span>
                    </div>
                </div>
                <div class="template-card-actions">
                    <button class="btn-icon" onclick="openTemplateModal('${t.id}')">✏️ Edit</button>
                    <button class="btn-icon danger" onclick="deleteTemplate('${t.id}')">🗑 Delete</button>
                </div>
            </div>
        </div>`;
    }).join('');
}

// ── Template dep-select: always renders a wrapper div, refreshed live after every add ──
// refreshDepSelects() rebuilds ALL sibling dep-selects in a container so every block
// always sees the correct predecessor options (including itself being added as the first item).
function refreshDepSelects(container, blockClass, nameInputClass, savedValues) {
    const allBlocks = Array.from(container.children).filter(el => el.classList.contains(blockClass));
    allBlocks.forEach((block, blockIdx) => {
        const wrapper = block.querySelector('.dep-select-wrapper');
        if (!wrapper) return;
        // preserve current selection before rebuilding
        const prevVal = wrapper.querySelector('select')?.value ?? '';
        const restoredVal = (savedValues && savedValues[block.id] != null)
            ? String(savedValues[block.id]) : prevVal;

        const siblings = allBlocks.filter(b => b !== block);
        const options = siblings.map(sib => {
            const nameEl = sib.querySelector(nameInputClass);
            const nm     = nameEl?.value?.trim() || '(unnamed)';
            const sibIdx = allBlocks.indexOf(sib);
            return `<option value="${sibIdx}" ${restoredVal === String(sibIdx) ? 'selected' : ''}>${nm}</option>`;
        }).join('');

        wrapper.innerHTML = `
            <div style="margin-top:8px;display:flex;align-items:center;gap:8px">
                <span style="font-size:10px;color:var(--warning);white-space:nowrap;flex-shrink:0">⛓ Depends On</span>
                <select class="tmpl-input tmpl-dep-select" style="flex:1;font-size:11px">
                    <option value="">None (independent)</option>
                    ${options}
                </select>
            </div>`;
    });
}

window.openTemplateModal = (templateId = null) => {
    _tmplEditId = templateId || null;
    document.getElementById('template-modal-title').innerText = templateId ? 'Edit Template' : 'Create Template';
    document.getElementById('tmpl-name').value = '';
    document.getElementById('tmpl-desc').value = '';
    document.getElementById('tmpl-milestones-container').innerHTML = '';
    _tmplMiIdx = 0; _tmplTiIdx = 0; _tmplSiIdx = 0;
    if (templateId) {
        const tmpl = db.templates.find(t => t.id === templateId);
        if (tmpl) {
            document.getElementById('tmpl-name').value = tmpl.name;
            document.getElementById('tmpl-desc').value = tmpl.description || '';
            // build savedValues map: blockId → dependsOnIdx for each level
            const mSaved = {};
            const container = document.getElementById('tmpl-milestones-container');
            // We'll restore after all blocks are added via a post-render pass
            tmpl.milestones.forEach((m, mi) => tmplAddMilestone(m, mi, tmpl.milestones));
        }
    }
    document.getElementById('template-modal').classList.remove('hidden');
};

document.getElementById('btn-cancel-template').addEventListener('click', () => {
    document.getElementById('template-modal').classList.add('hidden');
});

window.tmplAddMilestone = (data = null) => {
    const idx = ++_tmplMiIdx;
    const container = document.getElementById('tmpl-milestones-container');
    const div = document.createElement('div');
    div.className = 'tmpl-milestone-block';
    div.id = `tmpl-mi-${idx}`;
    div.innerHTML = `
        <div class="tmpl-milestone-header">
            <span style="font-size:10px;color:var(--warning);font-weight:700;flex-shrink:0">🏁 MILESTONE</span>
            <input class="tmpl-input tmpl-name-input" id="tmpl-mi-name-${idx}" placeholder="Milestone name…"
                value="${data?.name || ''}" oninput="refreshDepSelects(document.getElementById('tmpl-milestones-container'),
                    'tmpl-milestone-block','.tmpl-name-input')">
            <button class="tmpl-remove-btn" onclick="tmplRemoveMilestone('tmpl-mi-${idx}')">×</button>
        </div>
        <div class="dep-select-wrapper"></div>
        <div id="tmpl-tasks-${idx}" style="margin-top:8px"></div>
        <button class="tmpl-add-btn" onclick="tmplAddTask(${idx})">+ Add Task</button>`;
    container.appendChild(div);
    // Refresh ALL milestone dep-selects now that this block is in the DOM
    refreshDepSelects(container, 'tmpl-milestone-block', '.tmpl-name-input',
        data?.dependsOnIdx != null ? { [`tmpl-mi-${idx}`]: data.dependsOnIdx } : null);
    if (data?.tasks) data.tasks.forEach(t => tmplAddTask(idx, t));
};

window.tmplRemoveMilestone = (id) => {
    document.getElementById(id)?.remove();
    refreshDepSelects(
        document.getElementById('tmpl-milestones-container'),
        'tmpl-milestone-block', '.tmpl-name-input'
    );
};

window.tmplAddTask = (miIdx, data = null) => {
    const idx = ++_tmplTiIdx;
    const container = document.getElementById(`tmpl-tasks-${miIdx}`);
    if (!container) return;
    const div = document.createElement('div');
    div.className = 'tmpl-task-block';
    div.id = `tmpl-ti-${idx}`;
    div.setAttribute('data-mi', miIdx);
    div.innerHTML = `
        <div class="tmpl-label" style="margin-bottom:6px;color:var(--accent-primary)">Task</div>
        <div class="tmpl-task-row">
            <input class="tmpl-input tmpl-name-input" id="tmpl-ti-name-${idx}" placeholder="Task name…"
                value="${data?.name || ''}" oninput="refreshDepSelects(document.getElementById('tmpl-tasks-${miIdx}'),
                    'tmpl-task-block','.tmpl-name-input')">
            <div><div class="tmpl-label">Days</div>
                <input class="tmpl-input" type="number" min="1" id="tmpl-ti-dur-${idx}" value="${data?.duration ?? 5}" style="width:75px"></div>
            <div><div class="tmpl-label">Priority</div>
                <select class="tmpl-input" id="tmpl-ti-pri-${idx}" style="width:78px">
                    ${['Medium','High','Critical','Low'].map(p => `<option ${(data?.priority||'Medium')===p?'selected':''}>${p}</option>`).join('')}
                </select></div>
            <button class="tmpl-remove-btn" onclick="tmplRemoveTask('tmpl-ti-${idx}',${miIdx})">×</button>
        </div>
        <div class="dep-select-wrapper"></div>
        <div id="tmpl-subs-${idx}" style="margin-top:6px"></div>
        <button class="tmpl-add-btn" style="font-size:10px;padding:3px 8px" onclick="tmplAddSubtask(${idx})">+ Add Subtask</button>`;
    container.appendChild(div);
    // Refresh ALL task dep-selects in this milestone
    refreshDepSelects(container, 'tmpl-task-block', '.tmpl-name-input',
        data?.dependsOnIdx != null ? { [`tmpl-ti-${idx}`]: data.dependsOnIdx } : null);
    if (data?.subtasks) data.subtasks.forEach(s => tmplAddSubtask(idx, s));
};

window.tmplRemoveTask = (id, miIdx) => {
    document.getElementById(id)?.remove();
    const container = document.getElementById(`tmpl-tasks-${miIdx}`);
    if (container) refreshDepSelects(container, 'tmpl-task-block', '.tmpl-name-input');
};

window.tmplAddSubtask = (tiIdx, data = null) => {
    const idx = ++_tmplSiIdx;
    const container = document.getElementById(`tmpl-subs-${tiIdx}`);
    if (!container) return;
    const div = document.createElement('div');
    div.className = 'tmpl-subtask-block';
    div.id = `tmpl-si-${idx}`;
    div.innerHTML = `
        <div class="tmpl-label" style="margin-bottom:4px">Subtask</div>
        <div class="tmpl-subtask-row">
            <input class="tmpl-input tmpl-name-input" id="tmpl-si-name-${idx}" placeholder="Subtask name…"
                value="${data?.name || ''}" oninput="refreshDepSelects(document.getElementById('tmpl-subs-${tiIdx}'),
                    'tmpl-subtask-block','.tmpl-name-input')">
            <div><div class="tmpl-label">Days</div>
                <input class="tmpl-input" type="number" min="1" id="tmpl-si-dur-${idx}" value="${data?.duration ?? 3}" style="width:75px"></div>
            <div><div class="tmpl-label">Priority</div>
                <select class="tmpl-input" id="tmpl-si-pri-${idx}" style="width:78px">
                    ${['Medium','High','Critical','Low'].map(p => `<option ${(data?.priority||'Medium')===p?'selected':''}>${p}</option>`).join('')}
                </select></div>
            <button class="tmpl-remove-btn" onclick="tmplRemoveSubtask('tmpl-si-${idx}','tmpl-subs-${tiIdx}')">×</button>
        </div>
        <div class="dep-select-wrapper"></div>`;
    container.appendChild(div);
    refreshDepSelects(container, 'tmpl-subtask-block', '.tmpl-name-input',
        data?.dependsOnIdx != null ? { [`tmpl-si-${idx}`]: data.dependsOnIdx } : null);
};

window.tmplRemoveSubtask = (id, containerId) => {
    document.getElementById(id)?.remove();
    const container = document.getElementById(containerId);
    if (container) refreshDepSelects(container, 'tmpl-subtask-block', '.tmpl-name-input');
};

window.saveTemplate = () => {
    const name = document.getElementById('tmpl-name').value.trim();
    if (!name) { showToast('Template name is required', 'error'); return; }
    const milestones = [];
    document.querySelectorAll('#tmpl-milestones-container > .tmpl-milestone-block').forEach((mBlock) => {
        const miIdx  = mBlock.id.replace('tmpl-mi-', '');
        const miName = document.getElementById(`tmpl-mi-name-${miIdx}`)?.value?.trim();
        if (!miName) return;
        const mDepSel = mBlock.querySelector('.tmpl-dep-select');
        const mDepIdx = mDepSel?.value !== '' ? parseInt(mDepSel.value) : null;
        const tasks = [];
        mBlock.querySelectorAll('.tmpl-task-block').forEach(tBlock => {
            const tiIdx = tBlock.id.replace('tmpl-ti-', '');
            const tName = document.getElementById(`tmpl-ti-name-${tiIdx}`)?.value?.trim();
            if (!tName) return;
            const dur = parseInt(document.getElementById(`tmpl-ti-dur-${tiIdx}`)?.value) || 5;
            const pri = document.getElementById(`tmpl-ti-pri-${tiIdx}`)?.value || 'Medium';
            const tDepSel = tBlock.querySelector('.tmpl-dep-select');
            const tDepIdx = tDepSel?.value !== '' ? parseInt(tDepSel.value) : null;
            const subtasks = [];
            tBlock.querySelectorAll('.tmpl-subtask-block').forEach(sBlock => {
                const siIdx = sBlock.id.replace('tmpl-si-', '');
                const sName = document.getElementById(`tmpl-si-name-${siIdx}`)?.value?.trim();
                if (!sName) return;
                const sDur = parseInt(document.getElementById(`tmpl-si-dur-${siIdx}`)?.value) || 3;
                const sPri = document.getElementById(`tmpl-si-pri-${siIdx}`)?.value || 'Medium';
                const sDepSel = sBlock.querySelector('.tmpl-dep-select');
                const sDepIdx = sDepSel?.value !== '' ? parseInt(sDepSel.value) : null;
                subtasks.push({ name:sName, duration:sDur, priority:sPri, dependsOnIdx:sDepIdx });
            });
            tasks.push({ name:tName, duration:dur, priority:pri, dependsOnIdx:tDepIdx, subtasks });
        });
        milestones.push({ name:miName, dependsOnIdx:mDepIdx, tasks });
    });
    if (!milestones.length) { showToast('Add at least one milestone', 'error'); return; }
    if (_tmplEditId) {
        const tmpl = db.templates.find(t => t.id === _tmplEditId);
        if (tmpl) { tmpl.name = name; tmpl.description = document.getElementById('tmpl-desc').value; tmpl.milestones = milestones; }
    } else {
        db.templates.push({ id: genId('tmpl'), name, description: document.getElementById('tmpl-desc').value, milestones });
    }
    saveDb();
    document.getElementById('template-modal').classList.add('hidden');
    renderTemplates();
    showToast(_tmplEditId ? 'Template updated!' : 'Template saved!');
    _tmplEditId = null;
};

window.deleteTemplate = (id) => {
    if (!confirm('Delete this template? This cannot be undone.')) return;
    db.templates = db.templates.filter(t => t.id !== id);
    saveDb();
    renderTemplates();
    showToast('Template deleted');
};

function populateTemplateSelect() {
    const sel = document.getElementById('create-template-select');
    if (!sel) return;
    sel.innerHTML = '<option value="">Start blank (no template)</option>';
    db.templates.forEach(t => {
        const mC = t.milestones.length;
        const tC = t.milestones.reduce((a,m) => a+m.tasks.length, 0);
        sel.innerHTML += `<option value="${t.id}">${t.name} (${mC}M / ${tC}T)</option>`;
    });
}

document.getElementById('create-template-select').addEventListener('change', () => {
    const sel     = document.getElementById('create-template-select');
    const preview = document.getElementById('create-template-preview');
    const tmpl    = db.templates.find(t => t.id === sel.value);
    if (!tmpl) { preview.innerText = ''; return; }
    const mC = tmpl.milestones.length;
    const tC = tmpl.milestones.reduce((a,m) => a+m.tasks.length, 0);
    const sC = tmpl.milestones.reduce((a,m) => a+m.tasks.reduce((b,tk) => b+(tk.subtasks||[]).length, 0), 0);
    preview.innerHTML = `Will scaffold <strong>${mC}</strong> milestone${mC!==1?'s':''}, <strong>${tC}</strong> task${tC!==1?'s':''}, <strong>${sC}</strong> subtask${sC!==1?'s':''}. Dates cascade from project start.`;
});

// ── Template instantiation ─────────────────────────────────────────────
function instantiateTemplate(templateId, projectId) {
    const tmpl = db.templates.find(t => t.id === templateId);
    if (!tmpl) return;
    const msIds = [], msEnds = [];
    tmpl.milestones.forEach((mDef, mi) => {
        const mId = genId('m');
        let mStart = mDef.dependsOnIdx != null && msEnds[mDef.dependsOnIdx]
            ? new Date(msEnds[mDef.dependsOnIdx])
            : mi > 0 && msEnds[mi-1] ? new Date(msEnds[mi-1]) : new Date();
        const milestoneObj = { id:mId, projectId, name:mDef.name, description:'', status:'Yet to start',
            predecessor_id: mDef.dependsOnIdx != null ? (msIds[mDef.dependsOnIdx]||null) : null };
        db.milestones.push(milestoneObj);
        msIds.push(mId);
        const tIds = [], tEnds = [];
        let mEnd = new Date(mStart);
        mDef.tasks.forEach((tDef, ti) => {
            const tId = genId('t');
            let tStart = tDef.dependsOnIdx != null && tEnds[tDef.dependsOnIdx]
                ? new Date(tEnds[tDef.dependsOnIdx])
                : ti > 0 && tEnds[ti-1] ? new Date(tEnds[ti-1]) : new Date(mStart);
            const tEnd = new Date(tStart); tEnd.setDate(tEnd.getDate() + (tDef.duration||5));
            db.tasks.push({ id:tId, milestoneId:mId, name:tDef.name, description:'', status:'Yet to start',
                priority:tDef.priority||'Medium',
                planned_start:tStart.toISOString().split('T')[0],
                planned_end:tEnd.toISOString().split('T')[0],
                actual_start:null, actual_end:null,
                predecessor_id:tDef.dependsOnIdx!=null?(tIds[tDef.dependsOnIdx]||null):null,
                requires_document:false, attachment_url:null });
            tIds.push(tId); tEnds.push(tEnd);
            if (tEnd > mEnd) mEnd = tEnd;
            const sIds = [], sEnds = [];
            (tDef.subtasks||[]).forEach((sDef, si) => {
                const sId = genId('s');
                let sStart = sDef.dependsOnIdx!=null && sEnds[sDef.dependsOnIdx]
                    ? new Date(sEnds[sDef.dependsOnIdx])
                    : si > 0 && sEnds[si-1] ? new Date(sEnds[si-1]) : new Date(tStart);
                const sEnd = new Date(sStart); sEnd.setDate(sEnd.getDate() + (sDef.duration||3));
                db.subtasks.push({ id:sId, taskId:tId, name:sDef.name, description:'', status:'Yet to start',
                    priority:sDef.priority||'Medium',
                    planned_start:sStart.toISOString().split('T')[0],
                    planned_end:sEnd.toISOString().split('T')[0],
                    actual_start:null, actual_end:null,
                    predecessor_id:sDef.dependsOnIdx!=null?(sIds[sDef.dependsOnIdx]||null):null });
                sIds.push(sId); sEnds.push(sEnd);
            });
        });
        milestoneObj.planned_start = mStart.toISOString().split('T')[0];
        milestoneObj.planned_end   = mEnd.toISOString().split('T')[0];
        msEnds.push(mEnd);
    });
}

// ─────────────────────────────────────────────
// BOOT
// ─────────────────────────────────────────────
renderApp();
renderBreadcrumb();
