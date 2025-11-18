package controller;

import controller.utente.MostraLibroServlet;
import model.carrelloService.Carrello;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.libroService.LibroDAO;
import model.libroService.Autore;
import model.utenteService.Utente;
import model.wishList.WishList;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

public class MostraLibroServletTest {

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {  //fail
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreWhatever");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(dispatcher);
        when(request.getParameter("isbn")).thenReturn("any-isbn");

        // mock LibroDAO construction to avoid DB access when servlet continues
        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById(anyString())).thenReturn(new Libro());
                    when(mock.getScrittura(anyString())).thenReturn(new ArrayList<>());
                })) {

            new MostraLibroServlet().doGet(request, response);

            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void showBookFromCart_setsLibroAndAutoriAndForwards() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Libro libroInCart = new Libro();
        libroInCart.setIsbn("111-AAA");

        RigaCarrello riga = new RigaCarrello();
        riga.setLibro(libroInCart);
        List<RigaCarrello> righe = new ArrayList<>();
        righe.add(riga);

        Carrello carrello = new Carrello();
        carrello.setRigheCarrello(righe);

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(session.getAttribute("carrello")).thenReturn(carrello);
        when(session.getAttribute("wishList")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("111-AAA");
        when(request.getRequestDispatcher("/WEB-INF/results/mostraLibro.jsp")).thenReturn(dispatcher);

        // mock LibroDAO construction for getScrittura call
        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> when(mock.getScrittura("111-AAA")).thenReturn(new ArrayList<Autore>()))) {

            new MostraLibroServlet().doGet(request, response);

            verify(request).setAttribute("libro", libroInCart);
            verify(request).setAttribute(eq("autori"), anyList());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }

    @Test
    public void showBookNotInCartOrWishlist_usesDaoAndForwards() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(session.getAttribute("carrello")).thenReturn(null);
        when(session.getAttribute("wishList")).thenReturn(null);
        when(request.getParameter("isbn")).thenReturn("999-XXX");
        when(request.getRequestDispatcher("/WEB-INF/results/mostraLibro.jsp")).thenReturn(dispatcher);

        Libro daoLibro = new Libro();
        daoLibro.setIsbn("999-XXX");

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    when(mock.doRetrieveById("999-XXX")).thenReturn(daoLibro);
                    when(mock.getScrittura("999-XXX")).thenReturn(new ArrayList<Autore>());
                })) {

            new MostraLibroServlet().doGet(request, response);

            verify(request).setAttribute("libro", daoLibro);
            verify(request).setAttribute(eq("autori"), anyList());
            verify(dispatcher, times(1)).forward(request, response);
        }
    }
}
