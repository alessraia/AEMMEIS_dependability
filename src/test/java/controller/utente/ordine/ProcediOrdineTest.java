package controller.utente.ordine;

import controller.utente.ordine.ProcediOrdine;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.*;
import model.carrelloService.RigaCarrello;
import model.libroService.Libro;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;

class ProcediOrdineTest {

    private ProcediOrdine servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servletUnderTest = new ProcediOrdine();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
    }


    /**
     * Flusso principale: utente standard/premium,
     * righeDisponibili -> calcolo sedi -> forward a procediOrdine.jsp
     */
    @Test
    void testDoGet_Success() throws ServletException, IOException {
        Utente user = new Utente();
        user.setTipo("standard");
        when(session.getAttribute("utente")).thenReturn(user);

        List<RigaCarrello> righeDisponibili = new ArrayList<RigaCarrello>();
        Libro libro = new Libro();
        libro.setDisponibile(true);
        RigaCarrello rigaCarrello = new RigaCarrello();
        rigaCarrello.setLibro(libro);
        rigaCarrello.setIdCarrello("1");
        righeDisponibili.add(rigaCarrello);

        when(session.getAttribute("righeDisponibili")).thenReturn(righeDisponibili);

        when(request.getRequestDispatcher("/WEB-INF/results/procediOrdine.jsp"))
                .thenReturn(dispatcher);

        servletUnderTest.doGet(request, response);

        verify(dispatcher).forward(request, response);
    }
}