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
}
