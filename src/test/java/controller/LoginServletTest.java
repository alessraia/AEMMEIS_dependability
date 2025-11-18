package controller;

import static org.mockito.Mockito.*;

import controller.utente.LoginServlet;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.carrelloService.Carrello;
import model.carrelloService.CarrelloDAO;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import model.wishList.WishList;
import model.wishList.WishListDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.anyString;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

class LoginServletTest {

    private LoginServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    private UtenteDAO utenteDAO;
    private CarrelloDAO carrelloDAO;
    private WishListDAO wishListDAO;

    @BeforeEach
    void setUp() {
        servlet = new LoginServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        utenteDAO = mock(UtenteDAO.class);
        carrelloDAO = mock(CarrelloDAO.class);
        wishListDAO = mock(WishListDAO.class);

        servlet.setUtenteDAO(utenteDAO);
        servlet.setCarrelloDAO(carrelloDAO);
        servlet.setWishListDAO(wishListDAO);

        when(request.getSession()).thenReturn(session);
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);
    }

    @Test
    void testDoGet_InvalidForm() throws ServletException, IOException {
        when(request.getParameter("email")).thenReturn("invalid-email");
        when(request.getParameter("pw")).thenReturn("pwd");

        servlet.doGet(request, response);

        verify(response).sendRedirect("/WEB-INF/errorJsp/loginError.jsp");
    }

    @Test
    void testDoGet_InvalidCredentials() throws ServletException, IOException {
        when(request.getParameter("email")).thenReturn("mario@example.com");
        when(request.getParameter("pw")).thenReturn("password");

        when(utenteDAO.doRetrieveByEmailPassword("mario@example.com", "password")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/loginError.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(dispatcher).forward(request, response);
        verify(response, never()).sendRedirect("index.html");
    }

    @Test
    void testDoGet_SuccessWithCartMerge() throws ServletException, IOException {
        String email = "mario@example.com";
        String pw = "password";

        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("pw")).thenReturn(pw);
    // UtenteDAO returns a matching user for credentials and a user object for id
        Utente returned = new Utente();
        returned.setEmail(email);

    // la servlet passerà email + password HASHATA,
    // quindi accetto qualsiasi stringa come secondo argomento
        when(utenteDAO.doRetrieveByEmailPassword(eq(email), anyString())).thenReturn(returned);

        when(utenteDAO.doRetrieveById(email)).thenReturn(returned);

        // Local cart (in session) has one riga with isbn "ISBN-1" quantity 2
        Carrello local = new Carrello();
        List<RigaCarrello> localRighe = new ArrayList<>();
        RigaCarrello localRiga = new RigaCarrello();
        Libro libroLocal = new Libro();
        libroLocal.setIsbn("ISBN-1");
        localRiga.setLibro(libroLocal);
        localRiga.setQuantita(2);
        localRighe.add(localRiga);
        local.setRigheCarrello(localRighe);

        when(session.getAttribute("carrello")).thenReturn(local);

        // DB cart has one riga with same isbn quantity 1
        Carrello dbCart = new Carrello();
        List<RigaCarrello> dbRighe = new ArrayList<>();
        RigaCarrello dbRiga = new RigaCarrello();
        Libro libroDb = new Libro();
        libroDb.setIsbn("ISBN-1");
        dbRiga.setLibro(libroDb);
        dbRiga.setQuantita(1);
        dbRighe.add(dbRiga);
        dbCart.setRigheCarrello(dbRighe);
        dbCart.setIdCarrello("DB1");

        when(carrelloDAO.doRetriveByUtente(email)).thenReturn(dbCart);

        // WishList
        WishList wish = new WishList();
        when(wishListDAO.doRetrieveByEmail(email)).thenReturn(wish);

        servlet.doGet(request, response);
        verify(utenteDAO).doRetrieveByEmailPassword(eq(email), anyString());
        verify(utenteDAO).doRetrieveById(email);
// giusto per sicurezza:
        verify(dispatcher, never()).forward(any(), any());

        // Verify redirect to index
        verify(response).sendRedirect("index.html");

        // Verify that session attributes set (utente, carrello, wishList)
        verify(session).setAttribute("utente", returned);
        verify(session).setAttribute("carrello", dbCart);
        verify(session).setAttribute("wishList", wish);

        // Verify merge: quantity should be 3
        List<RigaCarrello> merged = dbCart.getRigheCarrello();
        // Should still contain exactly one riga with updated quantity 3
        assert merged.size() == 1;
        assert merged.get(0).getQuantita() == 3;
    }
}
