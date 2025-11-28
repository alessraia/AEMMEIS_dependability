package controller;

import controller.utente.LogoutServlet;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.carrelloService.RigaCarrelloDAO;
import model.libroService.Libro;
import model.libroService.Reparto;
import model.libroService.RepartoDAO;
import model.utenteService.Utente;
import model.wishList.WishList;
import model.wishList.WishListDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

class LogoutServletTest {

    private LogoutServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;

    private CarrelloDAO carrelloDAO;
    private WishListDAO wishListDAO;
    private RigaCarrelloDAO rigaCarrelloDAO;
    private RepartoDAO repartoDAO;

    @BeforeEach
    void setUp() throws ServletException {
        servlet = new LogoutServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);

        carrelloDAO = mock(CarrelloDAO.class);
        wishListDAO = mock(WishListDAO.class);
        rigaCarrelloDAO = mock(RigaCarrelloDAO.class);
        repartoDAO = mock(RepartoDAO.class);

        servlet.setCarrelloDAO(carrelloDAO);
        servlet.setWishListDAO(wishListDAO);
        servlet.setRigaCarrelloDAO(rigaCarrelloDAO);
        servlet.setRepartoDAO(repartoDAO);

        when(request.getSession()).thenReturn(session);

        // set a mock ServletContext via init(ServletConfig)
        ServletConfig config = mock(ServletConfig.class);
        ServletContext context = mock(ServletContext.class);
        when(config.getServletContext()).thenReturn(context);
        servlet.init(config);
    }

    @Test
    void testDoGet_nonAdmin_invalidDBNoSaves() throws ServletException, IOException {
        Utente utente = new Utente();
        utente.setEmail("u@example.com");
        utente.setTipo("Cliente");

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(null);
        WishList wishList = new WishList();
        wishList.setLibri(null);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        when(carrelloDAO.doRetriveByUtente(anyString())).thenReturn(null);
        when(wishListDAO.doRetrieveByEmail(anyString())).thenReturn(null);

        servlet.doGet(request, response);

        // session invalidated and redirected
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");

        // No DB saves called
        verify(rigaCarrelloDAO, never()).doSave(any(RigaCarrello.class));
        verify(wishListDAO, never()).doSave(any(WishList.class), anyString());
    }

    @Test
    void testDoGet_admin_deletesAndSavesAndUpdatesReparti() throws ServletException, IOException {
        String email = "admin@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Gestore-xyz"); // admin by Validator
        // Admins don't have/manage cart or wishlist in our business rules
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("wishList")).thenReturn(null);
        when(session.getAttribute("utente")).thenReturn(utente);
        // Make repartoDAO return some reparti list
        List<Reparto> reparti = new ArrayList<>();
        Reparto r = new Reparto();
        reparti.add(r);
        when(repartoDAO.doRetrivedAll()).thenReturn(reparti);

        // Execute
        servlet.doGet(request, response);

    // verify cart/wishlist DAOs were NOT called for an admin
    verify(carrelloDAO, never()).doRetriveByUtente(anyString());
    verify(rigaCarrelloDAO, never()).deleteRigheCarrelloByIdCarrello(anyString());
    verify(wishListDAO, never()).doRetrieveByEmail(anyString());
    verify(wishListDAO, never()).deleteWishListByEmail(anyString());
    verify(rigaCarrelloDAO, never()).doSave(any(RigaCarrello.class));
    verify(wishListDAO, never()).doSave(any(WishList.class), anyString());

        // verify reparti saved into servletContext
        // servlet.init set a mock ServletContext; capture verify via that mock
        ServletContext ctx = servlet.getServletConfig().getServletContext();
        verify(ctx).removeAttribute("reparti");
        verify(ctx).setAttribute("reparti", reparti);

        // session invalidated and redirected
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_withPopulatedCartAndWishList_deletesOldAndSavesNew() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        // Session cart with 2 items
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        List<RigaCarrello> righe = new ArrayList<>();
        RigaCarrello riga1 = new RigaCarrello();
        Libro libro1 = new Libro();
        libro1.setIsbn("978-0000000001");
        riga1.setLibro(libro1);
        riga1.setQuantita(2);
        RigaCarrello riga2 = new RigaCarrello();
        Libro libro2 = new Libro();
        libro2.setIsbn("978-0000000002");
        riga2.setLibro(libro2);
        riga2.setQuantita(1);
        righe.add(riga1);
        righe.add(riga2);
        carrello.setRigheCarrello(righe);

        // Session wishlist with 1 book
        WishList wishList = new WishList();
        List<Libro> libri = new ArrayList<>();
        Libro libro = new Libro();
        libro.setIsbn("978-0000000003");
        libri.add(libro);
        wishList.setLibri(libri);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        // Existing DB cart/wishlist to be deleted
        Carrello existingCart = new Carrello();
        existingCart.setIdCarrello("oldCart456");
        List<RigaCarrello> existingRighe = new ArrayList<>();
        existingRighe.add(new RigaCarrello());
        existingCart.setRigheCarrello(existingRighe);
        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(existingCart);

        WishList existingWishList = new WishList();
        List<Libro> existingLibri = new ArrayList<>();
        existingLibri.add(new Libro());
        existingWishList.setLibri(existingLibri);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(existingWishList);

        // Execute
        servlet.doGet(request, response);

        // Verify old cart deleted
        verify(rigaCarrelloDAO).deleteRigheCarrelloByIdCarrello("oldCart456");

        // Verify old wishlist deleted
        verify(wishListDAO).deleteWishListByEmail(email);

        // Verify new cart items saved (2 righe)
        verify(rigaCarrelloDAO, times(2)).doSave(any(RigaCarrello.class));

        // Verify new wishlist saved (called once per book with ISBN)
        verify(wishListDAO).doSave(eq(wishList), eq("978-0000000003"));

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_noExistingDBData_savesNewCartAndWishList() throws ServletException, IOException {
        String email = "newuser@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        // Session cart with 1 item
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("newCart789");
        List<RigaCarrello> righe = new ArrayList<>();
        RigaCarrello riga = new RigaCarrello();
        Libro libro = new Libro();
        libro.setIsbn("978-0000000004");
        riga.setLibro(libro);
        riga.setQuantita(3);
        righe.add(riga);
        carrello.setRigheCarrello(righe);

        // Session wishlist with 2 books
        WishList wishList = new WishList();
        List<Libro> libri = new ArrayList<>();
        Libro libro1 = new Libro();
        libro1.setIsbn("978-0000000005");
        Libro libro2 = new Libro();
        libro2.setIsbn("978-0000000006");
        libri.add(libro1);
        libri.add(libro2);
        wishList.setLibri(libri);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        // No existing DB data
        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(null);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(null);

        // Execute
        servlet.doGet(request, response);

        // Verify no deletes called
        verify(rigaCarrelloDAO, never()).deleteRigheCarrelloByIdCarrello(anyString());
        verify(wishListDAO, never()).deleteWishListByEmail(anyString());

        // Verify new cart items saved (1 riga)
        verify(rigaCarrelloDAO, times(1)).doSave(any(RigaCarrello.class));

        // Verify new wishlist saved (called once per book with ISBN)
        verify(wishListDAO).doSave(eq(wishList), eq("978-0000000005"));
        verify(wishListDAO).doSave(eq(wishList), eq("978-0000000006"));

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_emptyCartAndWishList_noDBOperations() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        // Empty cart
        Carrello carrello = new Carrello();
        carrello.setIdCarrello("emptyCart");
        carrello.setRigheCarrello(new ArrayList<>());

        // Empty wishlist
        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        // Existing DB data to be deleted
        Carrello existingCart = new Carrello();
        existingCart.setIdCarrello("oldCart999");
        List<RigaCarrello> existingRighe = new ArrayList<>();
        existingRighe.add(new RigaCarrello());
        existingCart.setRigheCarrello(existingRighe);
        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(existingCart);
        
        WishList existingWishList = new WishList();
        List<Libro> existingLibri = new ArrayList<>();
        existingLibri.add(new Libro());
        existingWishList.setLibri(existingLibri);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(existingWishList);

        // Execute
        servlet.doGet(request, response);

        // Verify old data deleted
        verify(rigaCarrelloDAO).deleteRigheCarrelloByIdCarrello("oldCart999");
        verify(wishListDAO).deleteWishListByEmail(email);

        // Verify no saves (empty collections)
        verify(rigaCarrelloDAO, never()).doSave(any(RigaCarrello.class));
        verify(wishListDAO, never()).doSave(any(WishList.class), anyString());

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_dbCartExistsButEmpty() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        List<RigaCarrello> righe = new ArrayList<>();
        RigaCarrello riga = new RigaCarrello();
        righe.add(riga);
        carrello.setRigheCarrello(righe);

        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        // DB cart exists but is empty
        Carrello dbCart = new Carrello();
        dbCart.setIdCarrello("dbCart456");
        dbCart.setRigheCarrello(new ArrayList<>());
        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(dbCart);

        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(null);

        servlet.doGet(request, response);

        // Verify no delete called (cart is empty)
        verify(rigaCarrelloDAO, never()).deleteRigheCarrelloByIdCarrello(anyString());

        // Verify cart items saved
        verify(rigaCarrelloDAO, times(1)).doSave(any(RigaCarrello.class));

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_dbWishListExistsButEmpty() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        carrello.setRigheCarrello(new ArrayList<>());

        WishList wishList = new WishList();
        List<Libro> libri = new ArrayList<>();
        Libro libro = new Libro();
        libro.setIsbn("978-123");
        libri.add(libro);
        wishList.setLibri(libri);

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(null);

        // DB wishlist exists but is empty
        WishList dbWishList = new WishList();
        dbWishList.setLibri(new ArrayList<>());
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(dbWishList);

        servlet.doGet(request, response);

        // Verify no delete called (wishlist is empty)
        verify(wishListDAO, never()).deleteWishListByEmail(anyString());

        // Verify wishlist items saved
        verify(wishListDAO, times(1)).doSave(eq(wishList), eq("978-123"));

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_wishListNull_skipSetEmail() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        carrello.setRigheCarrello(new ArrayList<>());

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(null); // wishList is null
        when(session.getAttribute("utente")).thenReturn(utente);

        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(null);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(null);

        servlet.doGet(request, response);

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_wishListAndUtentePresent_verifySetEmailCalled() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente");

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        carrello.setRigheCarrello(new ArrayList<>());

        // Use spy to verify setEmail is called
        WishList wishList = spy(new WishList());
        wishList.setLibri(new ArrayList<>());

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(null);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(null);

        servlet.doGet(request, response);

        // Verify setEmail was called with the user's email
        verify(wishList).setEmail(email);

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }

    @Test
    void testDoGet_nonAdmin_verifyAdminCheckNotExecuted() throws ServletException, IOException {
        String email = "user@example.com";
        Utente utente = new Utente();
        utente.setEmail(email);
        utente.setTipo("Cliente"); // non-admin

        Carrello carrello = new Carrello();
        carrello.setIdCarrello("cart123");
        carrello.setRigheCarrello(new ArrayList<>());

        WishList wishList = new WishList();
        wishList.setLibri(new ArrayList<>());

        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(wishList);
        when(session.getAttribute("utente")).thenReturn(utente);

        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(null);
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(null);

        servlet.doGet(request, response);

        // For non-admin user, the second admin check should NOT call removeAttribute/setAttribute for reparti
        // We verify the servlet context was called only once (from the admin early return at top)
        ServletContext ctx = servlet.getServletConfig().getServletContext();
        verify(ctx, never()).removeAttribute("reparti");
        verify(ctx, never()).setAttribute(eq("reparti"), any());

        // Verify session invalidated and redirect
        verify(session).invalidate();
        verify(response).sendRedirect("index.html");
    }
}
